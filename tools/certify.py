#!/usr/bin/env python3
"""Certification gate for StatFormal.

Trust model
-----------
* `StatFormal/**/Statements.lean` are the TRUSTED specification (definitions + claims as `Prop`s).
  They are written/approved by a human and hashed in `certify/statements.lock`.
* Every other `.lean` file is UNTRUSTED proof material (may be AI-written).
* `certify/targets.toml` maps each certified theorem to the frozen claim it must prove.

`check` fails unless ALL of:
  1. every Statements.lean matches its approved hash (no silent statement drift), and so does every
     local file it imports, transitively (definitions used by a claim are part of the spec);
  2. Statements.lean files contain no `sorry`, `axiom`, `opaque`, `implemented_by`, `extern`
     and proof files contain no `sorry`/`admit`/`axiom`/`native_decide`/`implemented_by`/
     `extern`/`debug.skipKernelTC`/`unsafe` (allow-list per target via `allow = [...]`);
  3. `lake build` succeeds;
  4. for every target, `example : <claim> := <theorem>` typechecks (the theorem proves exactly
     the frozen claim, not a variant), and `#print axioms` is within
     {propext, Classical.choice, Quot.sound}.

Usage:  tools/certify.py check | approve [Statements paths ...] [--note "who/why"] | status
"""
import hashlib, json, re, subprocess, sys, tomllib, datetime, pathlib, os

ROOT = pathlib.Path(__file__).resolve().parent.parent
LOCK = ROOT / "certify" / "statements.lock"
TARGETS = ROOT / "certify" / "targets.toml"
STD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
BAN_STMT = [r"\bsorry\b", r"^\s*axiom\b", r"\bopaque\b", r"implemented_by", r"@\[extern"]
BAN_PROOF = [r"\bsorry\b", r"\badmit\b", r"^\s*axiom\b", r"native_decide", r"implemented_by",
             r"@\[extern", r"skipKernelTC", r"^\s*unsafe\b"]
ENV = dict(os.environ, PATH=str(pathlib.Path.home() / ".elan/bin") + ":" + os.environ["PATH"])


def strip_comments(s):
    s = re.sub(r"/-.*?-/", "", s, flags=re.S)
    return re.sub(r"--.*", "", s)


def stmt_files():
    return sorted(p for p in (ROOT / "StatFormal").rglob("Statements.lean"))


def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def load_lock():
    return json.loads(LOCK.read_text()) if LOCK.exists() else {}


def local_deps(p, seen=None):
    """Transitive closure of the StatFormal.* modules imported by `p` (paths relative to ROOT).
    A frozen statement that imports a definition from an untrusted file would otherwise let that
    file change the meaning of the claim without touching the statement's hash."""
    seen = set() if seen is None else seen
    for m in re.findall(r"^\s*import\s+(StatFormal\.[\w.]+)", p.read_text(), flags=re.M):
        q = ROOT / (m.replace(".", "/") + ".lean")
        rel = str(q.relative_to(ROOT))
        if q.exists() and rel not in seen:
            seen.add(rel)
            local_deps(q, seen)
    return seen


def dep_digests(p):
    return {d: digest(ROOT / d) for d in sorted(local_deps(p))}


def approve(note, only=()):
    lock = load_lock()
    for p in stmt_files():
        if only and not any(str(p).endswith(o) for o in only):
            continue
        rel = str(p.relative_to(ROOT))
        h = digest(p)
        deps = dep_digests(p)
        if lock.get(rel, {}).get("sha256") != h or lock.get(rel, {}).get("deps", {}) != deps:
            lock[rel] = {"sha256": h, "deps": deps,
                         "approved": datetime.date.today().isoformat(), "note": note}
            print(f"approved {rel}" + (f" (+ {len(deps)} locked imports)" if deps else ""))
    LOCK.write_text(json.dumps(lock, indent=2) + "\n")


def scan(paths, patterns, allow=()):
    bad = []
    for p in paths:
        txt = strip_comments(p.read_text())
        for pat in patterns:
            if any(re.search(pat, a) for a in allow):
                continue
            for m in re.finditer(pat, txt, flags=re.M):
                line = txt[: m.start()].count("\n") + 1
                bad.append(f"{p.relative_to(ROOT)}:{line}: forbidden `{m.group(0).strip()}`")
    return bad


def check():
    fails = []
    lock = load_lock()
    for p in stmt_files():
        rel = str(p.relative_to(ROOT))
        if rel not in lock:
            fails.append(f"{rel}: statements never approved (run `approve` after human review)")
        elif lock[rel]["sha256"] != digest(p):
            fails.append(f"{rel}: STATEMENT CHANGED since approval {lock[rel]['approved']} — needs human re-review")
        else:
            # every local file the statement imports is part of the specification
            now = dep_digests(p)
            locked = lock[rel].get("deps")
            if locked is None:
                locked = {d: digest(ROOT / d) for d in now if d.endswith("/Statements.lean")}
            if now != locked:
                changed = sorted(set(now.items()) ^ set(locked.items()))
                fails.append(f"{rel}: imported definitions changed or unlocked since approval "
                             f"({', '.join(sorted({d for d, _ in changed}))}) — needs human re-review")
    targets = tomllib.loads(TARGETS.read_text()).get("target", [])
    allow = [a for t in targets for a in t.get("allow", [])]
    fails += scan(stmt_files(), BAN_STMT)
    proofs = [p for p in (ROOT / "StatFormal").rglob("*.lean") if p.name != "Statements.lean"]
    fails += scan(proofs, BAN_PROOF, allow)
    b = subprocess.run(["lake", "build"], cwd=ROOT, env=ENV, capture_output=True, text=True)
    if b.returncode != 0:
        fails.append("lake build failed:\n" + b.stdout[-3000:] + b.stderr[-2000:])
    else:
        mods = sorted({t["module"] for t in targets})
        audit = "\n".join(f"import {m}" for m in mods) + "\n"
        for t in targets:
            audit += f"example : {t['claim']} := {t['theorem']}\n#print axioms {t['theorem']}\n"
        af = ROOT / ".certify_audit.lean"
        af.write_text(audit)
        r = subprocess.run(["lake", "env", "lean", str(af)], cwd=ROOT, env=ENV, capture_output=True, text=True)
        af.unlink()
        out = r.stdout + r.stderr
        # Lean reports errors as `<file>:<line>:<col>: error`; a bare substring test would also
        # match theorem names such as `ext_solver_error` (false failure found 2026-10-13).
        if r.returncode != 0 or re.search(r":\d+:\d+: error", out):
            fails.append("claim/theorem mismatch or audit error:\n" + out[-3000:])
        for t in targets:
            m = re.search(rf"'{re.escape(t['theorem'])}' depends on axioms: \[(.*?)\]", out, re.S)
            if m:
                ax = {a.strip() for a in m.group(1).split(",") if a.strip()}
                extra = ax - STD_AXIOMS - set(t.get("allow_axioms", []))
                if extra:
                    fails.append(f"{t['theorem']}: non-standard axioms {sorted(extra)}")
            elif f"'{t['theorem']}' does not depend on any axioms" not in out:
                fails.append(f"{t['theorem']}: axiom audit missing")
    if fails:
        print("CERTIFICATION FAILED\n" + "\n".join(" - " + f for f in fails))
        sys.exit(1)
    print(f"CERTIFIED: {len(targets)} targets; statements frozen; axioms within {sorted(STD_AXIOMS)}")


if __name__ == "__main__":
    cmd = sys.argv[1] if len(sys.argv) > 1 else "check"
    if cmd == "approve":
        args = sys.argv[2:]
        note = args[args.index("--note") + 1] if "--note" in args else ""
        only = [a for i, a in enumerate(args) if a != "--note" and (i == 0 or args[i - 1] != "--note")]
        approve(note, only)
    elif cmd == "status":
        print(json.dumps(load_lock(), indent=2))
    else:
        check()
