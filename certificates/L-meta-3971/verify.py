from pathlib import Path
import os, subprocess, sys, tempfile

sources = Path(__file__).resolve().parent / 'src'
project = Path(sys.argv[1]).resolve()
modules = (sources.parent / 'modules.txt').read_text().splitlines()
lean = subprocess.check_output(['lake', 'env', 'which', 'lean'], cwd=project, text=True).strip()
libraries = subprocess.check_output(['lake', 'env', 'printenv', 'LEAN_PATH'], cwd=project, text=True).strip()
with tempfile.TemporaryDirectory(prefix='petersen-proof-') as output:
    env = {**os.environ, 'LEAN_PATH': output + os.pathsep + libraries}
    for module in modules:
        print(module, flush=True)
        subprocess.run([lean, '-j', '2', '-R', str(sources), '-o',
                        str(Path(output) / (module + '.olean')), str(sources / (module + '.lean'))],
                       env=env, cwd=project, check=True)
