"""Recheck HoshinoStarry's L-meta-10830 proof from open-goat/pequalnp-proofs PR 14995.

Use the project's Lean checkout with its dependencies built. Pass the downloaded
L_meta_10830.lean from commit f1aef8b2abfe52760a79d8971a1d6d7160cb7a7b.
The original proof is by HoshinoStarry and credits earlier project authors.
This replay changes compilation boundaries while retaining the proof terms.
"""
import argparse
from concurrent.futures import ThreadPoolExecutor
import hashlib
import os
from pathlib import Path
import re
import subprocess
import tempfile

SOURCE_SHA256 = "a8ffbf28022e6e192455726a97d982a17378056a82a05fcd9d744c5b0804a39f"
NAMESPACE = "PEqualNP.Outside.L_meta_10830"
END = f"end {NAMESPACE}\n"
OPTIONS = "set_option maxRecDepth 32768 in\nset_option maxHeartbeats 0 in\n"


def header(imports):
    return "".join(f"import {name}\n" for name in imports) + f"namespace {NAMESPACE}\n"


def modules(source):
    if hashlib.sha256(source).hexdigest() != SOURCE_SHA256:
        raise ValueError("Source does not match the published proof at the pinned commit.")
    original = source.decode("utf-8")
    core, concrete = original.split(OPTIONS + "theorem ls17 :", 1)
    concrete = "theorem ls17 :" + concrete
    forest, end_proof = concrete.split("theorem fromLower ", 1)
    flags = re.M | re.S
    definitions = re.findall(r"^def .+?(?=^def |^set_option |^theorem |\Z)", forest, flags)
    # The original file interleaves large arithmetic checks and their mathematical consequences.
    declarations = re.finditer(r"^theorem (\w+)\s*:(.*?)(?=^set_option|^def |^theorem |^end |\Z)", forest, flags)
    code = {"ForestCore10830": core + "\n" + END}
    code["ForestData10830"] = header(["ForestCore10830"]) + "\n".join(definitions) + "\n" + END
    pieces = {}
    derived = []
    weight = {}
    nblocks = 0
    for declaration in declarations:
        body = OPTIONS + declaration[0].strip() + "\n"
        tag = re.fullmatch(r"b([sm]\d+)_(\d+)_(\d+)", declaration[1])
        if tag is None:
            derived.append(body)
            continue
        nblocks += 1
        size = int(re.search(r" : block \w+ \d+ \d+ (\d+) = true", declaration[0])[1])
        key = "Arithmetic10830" + tag[1]
        if size > 43:
            key += "p" + tag[2] + "s" + tag[3]
        pieces.setdefault(key, []).append(body)
        weight[key] = weight.get(key, 0) + size
    if (len(definitions), nblocks, len(pieces), sum(weight.values())) != (439, 128, 73, 5599):
        raise ValueError("Unexpected declaration inventory in the pinned proof.")
    for key, bodies in pieces.items():
        code[key] = header(["ForestData10830"]) + "open PEqualNP.CircuitLowerBounds\n" + "".join(bodies) + END
    code["Rechecked10830"] = (header(pieces) + "open PEqualNP.CircuitLowerBounds\n"
                               + "".join(derived) + "theorem fromLower " + end_proof
                               + f"\n#print axioms {NAMESPACE}\n")
    return code, sorted(pieces, key=weight.get, reverse=True)


def main():
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument("source", type=Path)
    cli.add_argument("lean_project", type=Path, help="lean/ directory containing the lakefile and the built project")
    cli.add_argument("--workers", type=int, default=4)
    args = cli.parse_args()
    if args.workers < 1:
        cli.error("--workers must be positive")
    project = args.lean_project.resolve()
    code, shards = modules(args.source.read_bytes())
    with tempfile.TemporaryDirectory(prefix="pequalnp-10830-") as tmp:
        directory = Path(tmp).resolve()
        for name, content in code.items():
            (directory / (name + ".lean")).write_text(content, encoding="utf-8")
        def lake_value(cmd):
            return subprocess.check_output(["lake", "env", *cmd], cwd=project, text=True).strip()
        lean = lake_value(["which", "lean"])
        env = os.environ.copy()
        env["LEAN_PATH"] = str(directory) + os.pathsep + lake_value(["printenv", "LEAN_PATH"])
        def build(name):
            source = directory / (name + ".lean")
            result = subprocess.run([lean, "-j", "2", "-R", str(directory), "-o", str(source.with_suffix(".olean")), str(source)],
                                    cwd=project, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
            if result.returncode:
                raise RuntimeError(f"{name} failed\n{result.stdout[-5000:]}")
            return result.stdout
        build("ForestCore10830")
        build("ForestData10830")
        with ThreadPoolExecutor(max_workers=args.workers) as pool:
            for _ in pool.map(build, shards):
                pass
        output = build("Rechecked10830")
        audit = re.search(r"'PEqualNP\.Outside\.L_meta_10830' depends on axioms: \[([^]]*)\]", output)
        if audit is None or set(audit[1].split(", ")) != {"propext", "Classical.choice", "Quot.sound"}:
            raise RuntimeError("Unexpected axiom audit\n" + output[-2000:])
        print(audit[0], flush=True)
        exact_file = Path(__file__).resolve().with_name("ExactMinimum10831.lean")
        (directory / exact_file.name).write_bytes(exact_file.read_bytes())
        exact_output = build("ExactMinimum10831")
        for theorem in ("exact_minimum", "no_fourteen"):
            line = re.search(rf"'Simlowker10831\.{theorem}' depends on axioms: \[([^]]*)\]", exact_output)
            if line is None or set(line[1].split(", ")) != {"propext", "Classical.choice", "Quot.sound"}:
                raise RuntimeError("Unexpected exact minimum audit\n" + exact_output[-2000:])
            print(line[0])


if __name__ == "__main__":
    main()
