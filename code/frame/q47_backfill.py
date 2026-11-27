"""Regenerate selected historical Q47 proof traces locally and verify the compressed replacements.

The compact manifest identifies each selected leaf by case, original root, cube and
CNF digest. Store one zstd frame per distinct proof and one durable SQLite receipt
per verified formula. A completed row is published only after the artifact exists.
"""
import argparse
from concurrent.futures import FIRST_COMPLETED, ProcessPoolExecutor, wait
from contextlib import ExitStack
import fcntl
import gzip
import hashlib
import json
import os
from pathlib import Path
import sqlite3
import subprocess
from tempfile import TemporaryDirectory
import time

import q47_batch
import run_hard

ROOT = Path(__file__).resolve().parents[2]
TOOLS = ROOT/'tools'


def file_hash(path):
    with path.open('rb') as f:
        return hashlib.file_digest(f,'sha256').hexdigest()


def checked(cnf, proof, *options):
    result=subprocess.run([TOOLS/'drat-trim',cnf,proof,'-w',*options],capture_output=True)
    return result.returncode==0 and b's VERIFIED' in result.stdout.splitlines()


def compress(src,dst):
    subprocess.run(['zstd','-q','--single-thread','-3',src,'-o',dst],check=True)


def decompress(src,dst):
    with dst.open('wb') as writer:
        subprocess.run(['zstd','-dc',src],stdout=writer,check=True)


def formula_for(job):
    case=tuple(job['case'])
    _,root=q47_batch.build(case)
    if hashlib.sha256(root).hexdigest()!=job['root']:raise ValueError('root digest mismatch')
    if job['cube']:
        # The old four-bit local retries used the original run_hard encoder.
        if job['ledger']!='build/q47-local-retries/attempts.jsonl':
            raise ValueError('unsupported missing cube encoder')
        run_hard.init(47,24,0,'',True)
        _,text=run_hard.build(case,job['cube'])
        data=text.encode()
    else:
        data=root
    if hashlib.sha256(data).hexdigest()!=job['cnf']:raise ValueError('selected formula digest mismatch')
    return data


def archive_path(out,proof):
    return out/'proofs'/proof[:2]/(proof+'.drat.zst')


def generate(job,out):
    start=time.monotonic()
    cpu_start=q47_batch.child_cpu()
    with TemporaryDirectory(dir=out/'work') as d:
        work=Path(d);cnf=work/'formula.cnf';cnf.write_bytes(formula_for(job))
        raw=work/'raw.drat';trim=work/'trim.drat'
        result=subprocess.run([TOOLS/'cadical','-q',cnf,raw],capture_output=True)
        if result.returncode!=20:raise RuntimeError(('solver outcome',result.returncode,result.stderr[-400:]))
        original=file_hash(raw)
        if not checked(cnf,raw,'-C','-l',trim):raise ValueError('regenerated original did not verify')
        candidates=[]
        for proof in [raw,trim]:
            packed=proof.with_suffix('.zst');compress(proof,packed)
            candidates.append((packed.stat().st_size,proof,packed))
        for size,proof,packed in sorted(candidates):
            restored=work/'unpacked.drat'
            decompress(packed,restored)
            digest=file_hash(restored)
            if digest!=file_hash(proof):raise ValueError('compressed proof roundtrip mismatch')
            if proof==trim and not checked(cnf,restored):continue
            # For raw, byte-for-byte equality binds this file to the successful
            # original check above, even if the trimmed trace failed direct replay.
            dst=archive_path(out,digest)
            dst.parent.mkdir(exist_ok=True,parents=True)
            packed_hash=file_hash(packed)
            try:
                os.link(packed,dst)
            except FileExistsError:
                if file_hash(dst)!=packed_hash:raise ValueError('content-address collision')
            return dict(cnf=job['cnf'],original=original,proof=digest,packed_sha256=packed_hash,
                        raw_bytes=raw.stat().st_size,proof_bytes=restored.stat().st_size,packed_bytes=size,
                        trimmed=int(proof==trim),child_cpu=q47_batch.child_cpu()-cpu_start,elapsed=time.monotonic()-start)
    raise ValueError('no checked replacement')


def selection(manifest):
    jobs={}
    with gzip.open(manifest,'rt') as stream:
        for line in stream:
            root=json.loads(line)
            for cube,r in root['leaves']:
                if 'regenerate_bytes' not in r:continue
                j=dict(case=root['case'],cube=cube,root=root['root'],cnf=r['cnf'],historic=r['proof'],
                       ledger=r['ledger'],historic_bytes=r['regenerate_bytes'])
                if j['cnf'] in jobs and jobs[j['cnf']]!=j:raise ValueError('conflicting task')
                jobs[j['cnf']]=j
    return jobs


def register(db,r):
    # Concurrent generators can independently verify the same formula. Keep
    # the first published proof and its original provenance.
    return db.execute('INSERT INTO receipts VALUES (:cnf,:original,:proof,:packed_sha256,:raw_bytes,:proof_bytes,'
                      ':packed_bytes,:trimmed,:child_cpu,:elapsed) ON CONFLICT(cnf) DO NOTHING',r).rowcount


def import_pilot(db,jobs,pilot,out):
    if not pilot:return
    existing={h for h, in db.execute('SELECT cnf FROM receipts')}
    for f in sorted(pilot.glob('*.json')):
        r=json.loads(f.read_text());h=r['root']
        if h in existing or h not in jobs:continue
        j=jobs[h]
        if j['historic']!=r['raw_sha256'] or j['case']!=r['case'] or j['cube']:raise ValueError('pilot identity mismatch')
        source=pilot/(r['proof']+'.drat.zst')
        with TemporaryDirectory(dir=out/'work') as d:
            cnf=Path(d)/'input.cnf';cnf.write_bytes(formula_for(j))
            restored=Path(d)/'proof';decompress(source,restored)
            if file_hash(restored)!=r['proof'] or not checked(cnf,restored):raise ValueError('pilot proof mismatch')
            dst=archive_path(out,r['proof']);dst.parent.mkdir(exist_ok=True,parents=True)
            packed_hash=file_hash(source)
            if not dst.exists():os.link(source,dst)
            elif file_hash(dst)!=packed_hash:raise ValueError('pilot archive conflict')
            register(db,dict(cnf=h,original=r['raw_sha256'],proof=r['proof'],packed_sha256=packed_hash,
                raw_bytes=r['historic_bytes'],proof_bytes=restored.stat().st_size,packed_bytes=source.stat().st_size,
                trimmed=int(r['proof']!=r['raw_sha256']),child_cpu=0.,elapsed=0.))
    db.commit()


def status(db,out,total,start,active,lane):
    n,raw,compressed,cpu=db.execute('SELECT count(*),sum(raw_bytes),sum(packed_bytes),sum(child_cpu) FROM receipts').fetchone()
    result=dict(total=total,verified=n,remaining=total-n,active_workers=active,raw_bytes=raw or 0,packed_bytes=compressed or 0,
                solver_checker_and_compression_cpu_hours=round((cpu or 0)/3600,3),updated_unix=time.time(),session_wall_s=round(time.monotonic()-start))
    path=out/('status.json' if lane=='all' else f'status-{lane}.json')
    temp=path.with_suffix('.new');temp.write_text(json.dumps(result,indent=2)+'\n');temp.replace(path)


def queue_order(jobs):
    # Work across encoder families, keeping consecutive cases with the same
    # deficits so workers reuse their expensive base formula. Exercise the
    # legacy cube encoder immediately.
    return sorted(jobs,key=lambda j:(not bool(j['cube']),j['case'][4:],-j['historic_bytes'],j['root']))


def backfill(args):
    out=args.out.resolve();out.mkdir(parents=True,exist_ok=True)
    start=time.monotonic()
    with ExitStack() as locks:
        lanes=('roots','cubes') if args.lane=='all' else (args.lane,)
        for lane in lanes:
            lock=locks.enter_context((out/f'run-{lane}.lock').open('a'))
            fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
        for d in ('work','proofs'):(out/d).mkdir(exist_ok=True)
        jobs=selection(args.manifest)
        fingerprint=hashlib.sha256(json.dumps(sorted(jobs.values(),key=lambda r:r['cnf']),sort_keys=True,separators=(',',':')).encode()).hexdigest()
        with sqlite3.connect(out/'receipts.sqlite') as db:
            db.execute('PRAGMA journal_mode=WAL')
            db.execute('CREATE TABLE IF NOT EXISTS selection (hash TEXT PRIMARY KEY)')
            previous=db.execute('SELECT hash FROM selection').fetchall()
            if previous and previous!=[(fingerprint,)]:raise ValueError('selected missing queue changed')
            if not previous:db.execute('INSERT INTO selection VALUES (?)',(fingerprint,))
            db.execute('CREATE TABLE IF NOT EXISTS receipts (cnf TEXT PRIMARY KEY, original TEXT, proof TEXT, packed_sha256 TEXT, raw_bytes INTEGER, proof_bytes INTEGER, packed_bytes INTEGER, trimmed INTEGER, child_cpu REAL, elapsed REAL)')
            db.commit()
            import_pilot(db,jobs,args.pilot,out)
            done=set()
            for h,proof,size in db.execute('SELECT cnf,proof,packed_bytes FROM receipts'):
                if archive_path(out,proof).stat().st_size!=size or h not in jobs:raise ValueError('missing or unexpected archived proof')
                done.add(h)
            queue=queue_order(j for h,j in jobs.items() if h not in done and (args.lane=='all' or ('cubes' if j['cube'] else 'roots')==args.lane))
            if args.max_jobs:queue=queue[:args.max_jobs]
            pending=iter(queue);active={};errors=[]
            with ProcessPoolExecutor(args.workers) as pool:
                def refill():
                    limit=args.workers
                    if args.worker_budget is not None:
                        limit=int(args.worker_budget.read_text())
                        if not 1<=limit<=args.workers:raise ValueError('invalid worker budget')
                    while len(active)<limit:
                        j=next(pending,None)
                        if j is None:return
                        if db.execute('SELECT 1 FROM receipts WHERE cnf=?',(j['cnf'],)).fetchone():
                            continue
                        active[pool.submit(generate,j,out)]=j
                refill();status(db,out,len(jobs),start,len(active),args.lane);last=time.monotonic()
                while active:
                    finished,_=wait(active,timeout=20,return_when=FIRST_COMPLETED)
                    for future in finished:
                        j=active.pop(future)
                        try:r=future.result()
                        except Exception as exc:
                            error=dict(cnf=j['cnf'],case=j['case'],cube=j['cube'],error=repr(exc))
                            with (out/'errors.jsonl').open('a') as f:f.write(json.dumps(error)+'\n')
                            errors.append(error)
                            if len(errors)>=8:raise RuntimeError(errors)
                        else:register(db,r)
                    db.commit();refill()
                    if time.monotonic()-last>=20:
                        status(db,out,len(jobs),start,len(active),args.lane);last=time.monotonic()
            status(db,out,len(jobs),start,0,args.lane)
            if errors:raise RuntimeError(errors)
            print('Verified selections in this session:',len(queue)-len(errors),flush=True)

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('manifest',type=Path);p.add_argument('out',type=Path)
    p.add_argument('--workers',type=int,choices=range(1,9),default=8)
    p.add_argument('--pilot',type=Path)
    p.add_argument('--max-jobs',type=int)
    p.add_argument('--worker-budget',type=Path)
    p.add_argument('--lane',choices=('roots','cubes','all'),default='all')
    backfill(p.parse_args())
