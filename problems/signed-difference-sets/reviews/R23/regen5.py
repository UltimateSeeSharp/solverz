"""Run solver/marows.py with its output redirected under reviews/R23/gen, then diff with lean/."""
import sys, importlib.util, pathlib, filecmp
root = pathlib.Path.cwd()
spec = importlib.util.spec_from_file_location('marows', root / 'solver' / 'marows.py')
mod = importlib.util.module_from_spec(spec); spec.loader.exec_module(mod)
mod.OUT_DIR = root / 'reviews/R23/gen/a/b/MaRows'
mod.main(mod.PER_PART)
for f in sorted(mod.OUT_DIR.iterdir()):
    g = root / 'lean/SignedDifferenceSets/MaRows' / f.name
    print(f.name, 'identical' if g.exists() and f.read_bytes() == g.read_bytes() else 'DIFFERS')
