"""Root-scoped coverage by independently replayed plain Q47 DRAT cores."""
from collections import defaultdict
from functools import lru_cache
from hashlib import sha256
from pathlib import Path
import hashlib
import gzip
import json
import os
import shutil
import subprocess
import tempfile

from check_q47_cube_core import clauses, replay
from run_hard import layer_vars
import q47_batch

ROOT = Path(__file__).resolve().parents[2]
DRAT = ROOT/'tools/drat-trim'


def covered(prefix, patterns):
    """Whether the entire binary subcube is covered by a union of masks/prefixes."""
    residual = set()
    for pattern in patterns:
        if any(y != '*' and x != y for x, y in zip(prefix, pattern)):
            continue
        suffix = pattern[len(prefix):].rstrip('*')
        if not suffix:
            return True
        residual.add(suffix)
    return _union(frozenset(residual))


@lru_cache(maxsize=16384)
def _union(patterns):
    if '' in patterns:
        return True
    if not patterns:
        return False
    # Branch only on a constrained bit; unconstrained runs can be long.
    pos = min(next(i for i, b in enumerate(p) if b != '*') for p in patterns)
    return all(_union(frozenset(p[pos+1:] for p in patterns if p[pos] in ('*', bit)))
               for bit in '01')


def _hash(path):
    with path.open('rb') as f:
        return hashlib.file_digest(f,'sha256').hexdigest()


def _cert_key(path):
    return sha256(b''.join(bytes.fromhex(_hash(path/name)) for name in
                           ('info.json','core.cnf','core.drat'))).hexdigest()


@lru_cache(maxsize=1)
def _checker_version():
    return [_hash(f) for f in (Path(__file__).with_name('check_q47_cube_core.py'),DRAT)]

@lru_cache(maxsize=8192)
def _validated(path, versions):
    if _cert_key(path) != path.name:
        raise ValueError(f'changed certificate {path}')
    # Registration replays the staged bytes before atomic publication. Bind
    # that receipt to every content hash and to the exact checker binary/code.
    marker=path/'replay.json'
    receipt=json.loads(marker.read_text()) if marker.exists() else None
    info = json.loads((path/'info.json').read_text())
    mask=info['mask'] if receipt==dict(certificate=path.name,checker=_checker_version()) else replay(path)
    return info['root_sha256'], tuple(info['case']), mask


def load(store, roots):
    result = defaultdict(set)
    if not store.exists():
        return result
    for path in store.iterdir():
        if path.name.startswith('.') or not path.is_dir():
            continue
        versions = tuple((s.st_ino,s.st_size,s.st_ctime_ns) for s in
                         ((path/n).stat() for n in ('info.json','core.cnf','core.drat')))
        root, case, mask = _validated(path, versions)
        if roots.get(case) != root:
            if case in roots:
                raise ValueError(f'wrong baseline for {path}')
            continue
        result[case].add(mask)
    return result


def publish(directory, store, root):
    info = json.loads((directory/'info.json').read_text())
    if info['root_sha256'] != root:
        raise ValueError('incorrect source root')
    store.mkdir(exist_ok=True, parents=True)
    with tempfile.TemporaryDirectory(dir=store, prefix='.new-') as tmp:
        stage = Path(tmp)/'cert'
        stage.mkdir()
        for name in ('core.cnf','core.drat','info.json'):
            shutil.copyfile(directory/name, stage/name)
        replay(stage)
        digest = _cert_key(stage)
        (stage/'replay.json').write_text(json.dumps(dict(certificate=digest,checker=_checker_version()))+'\n')
        destination = store/digest
        try:
            stage.rename(destination)
        except OSError:
            if not destination.is_dir() or _cert_key(destination) != digest:
                raise
    return destination


@lru_cache(maxsize=1)
def _baseline(case):
    base, data = q47_batch.build(case)
    return base, data, sha256(data).hexdigest()


def extract(row, root_hash, archives, store, work):
    """Reconstruct and hash the source cube, then trim and replay its certificate."""
    if row.get('encoding','plain') != 'plain' or row.get('kind','overnight') not in ('overnight','split'):
        raise ValueError('expected an archived plain baseline cube')
    if row.get('drat') != 'VERIFIED' or row['result'] != 'UNSAT':
        raise ValueError('expected a checked source proof')
    case = tuple(row['case'])
    bits = row['cube']
    if not bits or len(bits)%4 or set(bits)-set('01'):
        raise ValueError('invalid cube')
    base, root, digest = _baseline(case)
    if digest != root_hash or row.get('parent_sha256',digest) != digest:
        raise ValueError('root hash mismatch')
    vs = [v for j in range(1,len(bits)//4+1) for v in layer_vars(base,case,j)]
    units = [v if b=='1' else -v for v,b in zip(vs,bits,strict=True)]
    head,body = root.split(b'\n',1)
    top,n = head.split()[2:]
    data = b'p cnf '+top+b' '+str(int(n)+len(units)).encode()+b'\n'+body
    data += ''.join(f'{v} 0\n' for v in units).encode()
    if sha256(data).hexdigest() != row['cnf_sha256']:
        raise ValueError('source cube hash mismatch')
    cnf, proof = work/'input.cnf', work/'input.drat'
    cnf.write_bytes(data)
    archive = archives/row.get('archive_file',row['cnf_sha256']+'.drat')
    with proof.open('wb') as dst:
        if archive.suffix == '.zst':
            subprocess.run(['zstd','-dc',archive],stdout=dst,check=True)
        else:
            with (gzip.open(archive,'rb') if archive.suffix=='.gz' else archive.open('rb')) as src:
                shutil.copyfileobj(src,dst)
    if _hash(proof) != row['proof_sha256']:
        raise ValueError('source proof hash mismatch')
    core, trimmed = work/'core.cnf', work/'core.drat'
    ck = subprocess.run([DRAT,cnf,proof,'-w','-c',core,'-l',trimmed,'-C'],
                        capture_output=True,timeout=30)
    if ck.returncode or b's VERIFIED' not in ck.stdout.splitlines():
        raise ValueError('source proof did not verify')
    # Non-unit clauses are tested against the whole root by the independent replay.
    unit_clauses = {c[0] for c in clauses(core.read_bytes()) if len(c)==1}
    unit_clauses -= {int(line.split()[0]) for line in body.splitlines() if line.count(b' ')==1 and line.endswith(b' 0')}
    mask = ''.join(b if v in unit_clauses else '*' for v,b in zip(units,bits))
    if '*' not in mask:
        return mask, None
    info = dict(case=case, root_sha256=digest, source_sha256=row['cnf_sha256'],
                source_proof_sha256=row['proof_sha256'],bits=bits,mask=mask)
    (work/'info.json').write_text(json.dumps(info,sort_keys=True)+'\n')
    return mask, publish(work,store,digest)


def ledger_pieces(ordinary, masks, touched):
    """Materialise only ledger-frontier prefixes, even for very deep masks."""
    if not masks:
        return set()
    splits = {b[:i] for b in ordinary|touched for i in range(0,len(b),4)} | touched
    pieces = set()
    def visit(b):
        if b in ordinary:
            return
        if covered(b,masks):
            pieces.add(b)
        elif b in splits:
            for j in range(16):
                visit(b+format(j,'04b'))
    visit('')
    return pieces


class SiblingCores:
    """Check the exact root's masks before a solve; screen small plain siblings first."""

    def __init__(self, out, roots, max_bytes=256*1024):
        self.out = out
        self.store = out/'core-certificates'
        self.store.mkdir(exist_ok=True)
        self.screen = out/'core-screen'
        self.screen.mkdir(exist_ok=True)
        self.roots = roots
        self.max_bytes = max_bytes
        self.rows = defaultdict(dict)
        self.stamp = None
        self.masks = defaultdict(set)
        self.attempted = set()
        self.refresh()

    def refresh(self):
        stamp = self.store.stat().st_mtime_ns
        if stamp != self.stamp:
            self.masks = load(self.store,self.roots)
            self.stamp = stamp

    def add(self, row):
        c = tuple(row['case'])
        if (c in self.roots and row.get('result')=='UNSAT' and row.get('drat')=='VERIFIED'
                and row.get('encoding','plain')=='plain' and row.get('kind','overnight') in ('overnight','split')
                and row.get('cube') and 0 < row.get('proof_bytes',0) <= self.max_bytes
                and row.get('parent_sha256',self.roots[c])==self.roots[c]):
            self.rows[c][row['cnf_sha256']] = row

    def before(self, case, bits, ordinary=(), trials=1):
        self.refresh()
        root=self.roots[case]
        def hit():
            masks=self.masks.get(case)
            return bool(masks) and (covered(bits,masks) or
                    bool(ordinary) and covered(bits,(*masks,*ordinary)))
        if hit():
            confirm(self.store,case,root,self.masks[case])
            return True
        if not bits or not trials:
            return False
        # An ancestor's sibling can also exclude this descendant. Prefer
        # sources close to this cube, then smaller proofs at equal distance.
        candidates=[]
        for h,r in self.rows[case].items():
            b=r['cube']
            if h in self.attempted or len(b)>len(bits) or bits.startswith(b):
                continue
            if (self.screen/h).exists():
                self.attempted.add(h)
                continue
            mismatches=sum(x!=y for x,y in zip(b,bits))
            candidates.append((b[:-4]!=bits[:len(b)-4],mismatches,r['proof_bytes'],h,r))
        for _,_,_,h,r in sorted(candidates)[:trials]:
            self.attempted.add(h)
            try:
                with tempfile.TemporaryDirectory(dir=self.screen,prefix='.work-') as tmp:
                    mask,cert=extract(r,root,self.out/'proofs',self.store,Path(tmp))
                    receipt=Path(tmp)/'screen.json'
                    receipt.write_text(json.dumps(dict(source=h,root=root,mask=mask,
                         certificate=cert.name if cert else None))+'\n')
                    os.replace(receipt,self.screen/h)
            except (ValueError, OSError, subprocess.SubprocessError) as err:
                # No evidence was accepted. Fall through to the normal solve.
                import logging
                logging.getLogger(__name__).warning('Core screening failed for %s: %s',h,err)
                continue
            self.refresh()
            if hit():
                confirm(self.store,case,root,self.masks[case])
                return True
        return False


@lru_cache(maxsize=4096)
def _independent(path, version):
    # Used before crediting new coverage in the reconciled ledger. Repeat in
    # every fresh verifier process, even if a registration receipt exists.
    if _cert_key(path) != path.name:
        raise ValueError(f'certificate content hash differs for {path}')
    return replay(path)


def confirm(store, case, root, masks):
    remaining=set(masks)
    for path in store.iterdir():
        if path.name.startswith('.') or not path.is_dir():
            continue
        info=json.loads((path/'info.json').read_text())
        if (tuple(info['case']) != case or info['root_sha256'] != root or
                info['mask'] not in remaining):
            continue
        version=tuple((s.st_ino,s.st_size,s.st_ctime_ns) for s in
                      ((path/n).stat() for n in ('info.json','core.cnf','core.drat')))
        remaining.remove(_independent(path,version))
        if not remaining:
            return
    if remaining:
        raise ValueError(f'missing independently replayed mask for {case}')
