import os
import sys
import toml

t = toml.load(sys.stdin)

# Edit dependency paths
meta = t['package']['metadata']['microram']
microram_deps = set(meta.get('deps', ()))
discard_deps = []
for k, v in t['dependencies'].items():
    if k in microram_deps:
        # Adjust path dependencies, since the build will occur in a different
        # directory.
        if 'path' in v:
            v['path'] = os.path.join('../..', v['path'])
    else:
        discard_deps.append(k)
for k in discard_deps:
    del t['dependencies'][k]

# Adjust targets

t['package']['autobins'] = False
t['package']['autoexamples'] = False
t['package']['autotests'] = False
t['package']['autobenches'] = False

lib = t.setdefault('lib', {})
lib_path = lib.setdefault('path', 'src/lib.rs')
lib['path'] = os.path.join('../..', lib_path)

bins = t.setdefault('bin', [])
microram_bins = set(meta.get('bins', ()))
discard_bins = []
for i, b in enumerate(bins):
    if b['name'] in microram_bins:
        bin_path = b.setdefault('path', 'src/bin/%s.rs' % b['name'])
        b['path'] = os.path.join('../..', bin_path)
    else:
        discard_bins.append(i)
for i in reversed(discard_bins):
    del bins[i]

toml.dump(t, sys.stdout)
