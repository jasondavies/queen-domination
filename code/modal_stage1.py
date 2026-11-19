"""Run stage-1 parts for n = 28 on Modal (rented single-core cloud containers).  Ephemeral app: `modal run`.

This is the driver used for 7,457 of the 16,800 stage-1 parts of the n = 28 computation (data/n28/
modal_parts.tsv.xz, modal_calls.tsv).  For that run the two C programs carried their working names
lines2.c and lines_v.c; they are code/stage1.c and code/stage1_v.c, identical apart from comments and one
usage string, and the ledger's program name "lines2" refers to code/stage1.c.

usage:  modal run code/modal_stage1.py --jobs JOBFILE [--batch 8] [--conc 100] [--budget 7.0] [--procs 1]
JOBFILE lines: "PROG Z MOD PART OUTDIR" (PROG in lines2, lines_v).  Results are written into OUTDIR as
OUTDIR/z<Z>/part_<P>.{cand,s1log,done}; a part is skipped if its .done exists.  Every returned part is
verified locally (exit code, part/mod and colour split in the log, survivor count, SHA-256 of the candidate
list computed remotely and locally), the C sources are hashed locally and in the container, and the
container's binary SHA-256 is recorded.  Ledger: build/modal/modal_ledger.tsv (one line per part) and
build/modal/modal_calls.tsv (one line per call, with the in-container wall time used for the cost estimate);
the cumulative estimate is kept in build/modal/modal_cost.txt and dispatching stops at --budget (US dollars,
including the calls in flight).  Each container is limited to one physical core (cpu=(1, 1)).
"""
import modal, os, sys, time, hashlib, json, subprocess, re

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LED = os.path.join(ROOT, "build", "modal")      # ledgers and cost estimate (git-ignored)
N, G = 28, 14
CPU_RATE = 0.0473 / 3600     # $/core-s   (modal billing rates, 2026-11-19)
MEM_RATE = 0.008 / 3600      # $/GiB-s
MEM_GIB = 0.5
OVERHEAD_S = 15              # per call allowance for container start / scaledown (estimate)

image = (
    modal.Image.from_registry(
        "debian:bookworm-20251229-slim@sha256:d5d3f9c23164ea16f31852f95bd5959aad1c5e854332fe00f7b3a20fcc9f635c",
        add_python="3.12")
    .apt_install("gcc", "libc6-dev")
    .add_local_file(os.path.join(ROOT, "code/stage1.c"), "/opt/q/lines2.c", copy=True)
    .add_local_file(os.path.join(ROOT, "code/stage1_v.c"), "/opt/q/lines_v.c", copy=True)
    .run_commands(
        "gcc --version | head -1 > /opt/q/gcc.txt",
        "cd /opt/q && gcc -O2 -march=x86-64-v2 -o lines2 lines2.c && gcc -O2 -march=x86-64-v2 -o lines_v lines_v.c",
        "cd /opt/q && sha256sum lines2.c lines_v.c lines2 lines_v > /opt/q/SHA256")
)
app = modal.App("qd28-stage1", image=image)


@app.function(cpu=(1.0, 1.0), memory=512, timeout=3600, max_containers=100, retries=0, scaledown_window=10)
def run_parts(prog: str, z: int, mod: int, parts: list, procs: int = 2):
    import concurrent.futures as cf, platform
    t0 = time.time()
    binp = "/opt/q/" + prog
    def one(p):
        s = time.time()
        r = subprocess.run([binp, str(N), str(G), str(z), str(p), str(mod)], capture_output=True, text=True)
        return dict(part=p, rc=r.returncode, cand=r.stdout, log=r.stderr, wall=time.time() - s)
    with cf.ThreadPoolExecutor(procs) as ex:
        res = list(ex.map(one, parts))
    cpu = open("/proc/cpuinfo").read()
    m = re.search(r"model name\s*:\s*(.*)", cpu)
    lscpu = subprocess.run(["sh", "-c", "nproc; cat /sys/fs/cgroup/cpu.max 2>/dev/null; grep -m1 \"model name\" /proc/cpuinfo"], capture_output=True, text=True).stdout.replace("\n", " | ").replace("\t", " ")
    return dict(results=res, wall=time.time() - t0, sha=open("/opt/q/SHA256").read(), lscpu=lscpu,
                gcc=open("/opt/q/gcc.txt").read().strip(), cpu=m.group(1) if m else "?",
                ncpu=os.cpu_count())


def local_sha(path):
    return hashlib.sha256(open(path, "rb").read()).hexdigest()


def write_part(prog, z, mod, p, outdir, r):
    """verify one returned part and write run_s1.sh-format files; returns error string or None"""
    log = r["log"]
    if r["rc"] != 0: return "rc=%d" % r["rc"]
    if "time=" not in log: return "no time= in log"
    if not re.search(r"part %d/%d" % (p, mod), log): return "part/mod mismatch in log"
    if not re.search(r"z=\(%d,%d\)" % (z, G - z), log): return "z mismatch in log"
    ncand = sum(1 for l in r["cand"].splitlines() if l.startswith("C "))
    key = "surv=" if prog == "lines2" else "out="
    m = re.search(key + r"(\d+)", log)
    if not m or int(m.group(1)) != ncand: return "survivor count mismatch"
    for l in r["cand"].splitlines():
        f = l.split()
        if len(f) != 4 or f[0] != "C" or int(f[3]) != z: return "bad cand line"
    d = os.path.join(outdir, "z%d" % z); os.makedirs(d, exist_ok=True)
    f = os.path.join(d, "part_%d" % p)
    if os.path.exists(f + ".done"): return "already done locally (duplicate)"
    open(f + ".cand.tmp", "w").write(r["cand"])
    open(f + ".s1log", "w").write(log)
    if hashlib.sha256(r["cand"].encode()).hexdigest() != local_sha(f + ".cand.tmp"): return "sha mismatch"
    os.rename(f + ".cand.tmp", f + ".cand")
    sh = local_sha(f + ".cand")[:16]
    open(f + ".done", "w").write("%s %d %d %d %d %d cand=%d %s %s\n" % (prog, N, G, z, mod, p, ncand, sh, log.strip()))
    return None


@app.local_entrypoint()
def main(jobs: str, batch: int = 8, conc: int = 100, budget: float = 7.0, procs: int = 1, maxcalls: int = 0):
    srcsha = {"lines2.c": local_sha(os.path.join(ROOT, "code/stage1.c")), "lines_v.c": local_sha(os.path.join(ROOT, "code/stage1_v.c"))}
    todo = []
    for l in open(jobs):
        f = l.split()
        if not f: continue
        prog, z, mod, p, out = f[0], int(f[1]), int(f[2]), int(f[3]), f[4]
        if not os.path.isabs(out): out = os.path.join(ROOT, out)
        if os.path.exists(os.path.join(out, "z%d" % z, "part_%d.done" % p)): continue
        todo.append((prog, z, mod, p, out))
    # group into batches with the same (prog, z, mod, out)
    batches = []
    cur = []
    for j in todo:
        if cur and (j[0], j[1], j[2], j[4]) != (cur[0][0], cur[0][1], cur[0][2], cur[0][4]) or len(cur) >= batch:
            batches.append(cur); cur = []
        cur.append(j)
    if cur: batches.append(cur)
    if maxcalls: batches = batches[:maxcalls]
    print("parts to do: %d in %d calls" % (len(todo), len(batches)), flush=True)
    os.makedirs(LED, exist_ok=True)
    ledger = open(os.path.join(LED, "modal_ledger.tsv"), "a")
    calls = open(os.path.join(LED, "modal_calls.tsv"), "a")
    costf = os.path.join(LED, "modal_cost.txt")
    spent = float(open(costf).read().split()[0]) if os.path.exists(costf) else 0.0
    pending = {}; nb = 0; errors = 0; ok = 0
    t_start = time.time()
    while (nb < len(batches) or pending):
        ncalls_done = max(1, sum(1 for _ in open(os.path.join(LED, "modal_calls.tsv"))))  # calls of all runs
        mean_call = max(0.005, spent / ncalls_done) if spent > 0 else 0.005
        while nb < len(batches) and len(pending) < conc and spent + (len(pending) + 1) * mean_call < budget:
            b = batches[nb]; nb += 1
            fc = run_parts.spawn(b[0][0], b[0][1], b[0][2], [j[3] for j in b], procs)
            pending[fc.object_id] = (fc, b, time.time())
        if spent + (len(pending) + 1) * mean_call >= budget and nb < len(batches):
            print("BUDGET STOP: estimated spend %.3f + in-flight %d x %.4f >= %.2f; %d calls not dispatched" % (spent, len(pending), mean_call, budget, len(batches) - nb), flush=True)
            batches = batches[:nb]
        done_ids = []
        for cid, (fc, b, ts) in list(pending.items()):
            try:
                res = fc.get(timeout=0)
            except TimeoutError:
                continue
            except Exception as e:
                print("CALL ERROR %s %r" % (cid, e), flush=True); errors += 1
                spent += (time.time() - ts) * (CPU_RATE + MEM_RATE * MEM_GIB)   # conservative
                open(costf, "w").write("%.4f estimated USD\n" % spent)
                done_ids.append(cid); continue
            done_ids.append(cid)
            # source / binary hash check
            rsha = {l.split()[1]: l.split()[0] for l in res["sha"].splitlines()}
            if rsha.get("lines2.c") != srcsha["lines2.c"] or rsha.get("lines_v.c") != srcsha["lines_v.c"]:
                print("SOURCE HASH MISMATCH, discarding call", cid, flush=True); errors += 1; continue
            c = (res["wall"] + OVERHEAD_S) * (CPU_RATE + MEM_RATE * MEM_GIB)
            spent += c
            open(costf, "w").write("%.4f estimated USD\n" % spent)
            calls.write("%s\t%s\t%d\t%d\t%s\t%.1f\t%.5f\t%s\t%s\t%s\n" % (cid, b[0][0], b[0][1], b[0][2],
                        ",".join(str(j[3]) for j in b), res["wall"], c, res.get("lscpu", res["cpu"]), res["gcc"], rsha.get(b[0][0])))
            calls.flush()
            for j, r in zip(b, res["results"]):
                assert r["part"] == j[3]
                err = write_part(j[0], j[1], j[2], j[3], j[4], r)
                if err: print("PART ERROR %s z%d p%d: %s" % (j[0], j[1], j[3], err), flush=True); errors += 1
                else:
                    ok += 1
                    ledger.write("%s\t%d\t%d\t%d\t%s\t%.2f\t%s\t%s\n" % (j[0], j[1], j[2], j[3], cid, r["wall"], rsha.get(j[0]), os.path.relpath(j[4], ROOT)))
            ledger.flush()
        for cid in done_ids: pending.pop(cid, None)
        if done_ids:
            print("[%5.0fs] parts ok=%d errors=%d calls done=%d/%d pending=%d est.spend=$%.3f" % (
                time.time() - t_start, ok, errors, nb - len(pending), len(batches), len(pending), spent), flush=True)
        time.sleep(5)
    print("FINISHED ok=%d errors=%d est.spend=$%.3f" % (ok, errors, spent), flush=True)
