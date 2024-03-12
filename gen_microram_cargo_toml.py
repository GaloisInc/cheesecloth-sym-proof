import os
import sys
import toml

def convert(in_path, out_path, workspace_member_abs_paths=()):
    t = toml.load(open(in_path))

    rel_path = os.path.relpath(os.path.dirname(in_path), os.path.dirname(out_path))

    # Also migrate workspace members
    workspace_members = t.get('workspace', {}).get('members')
    if workspace_members is not None:
        workspace_member_abs_paths = set(
                os.path.abspath(os.path.join(os.path.dirname(in_path), member_path))
                for member_path in workspace_members)
        for member_path in workspace_members:
            member_in_path = os.path.join(os.path.dirname(in_path), member_path, 'Cargo.toml')
            member_out_path = os.path.join(os.path.dirname(out_path), member_path, 'Cargo.toml')
            convert(member_in_path, member_out_path, workspace_member_abs_paths)

    # Edit dependency paths
    meta = t.get('package', {}).get('metadata', {}).get('microram', {})
    microram_deps = set(meta.get('deps', ()))
    discard_deps = []
    for k, v in t.get('dependencies', {}).items():
        if k in microram_deps:
            # Adjust path dependencies, since the build will occur in a different
            # directory.
            if 'path' in v:
                abs_path = os.path.abspath(os.path.join(os.path.dirname(in_path), v['path']))
                if abs_path not in workspace_member_abs_paths:
                    v['path'] = os.path.join(rel_path, v['path'])
        else:
            discard_deps.append(k)
    for k in discard_deps:
        del t['dependencies'][k]

    # Remove features
    for name in meta.get('remove-features', ()):
        del t['features'][name]

    # Adjust targets

    t['package']['autobins'] = False
    t['package']['autoexamples'] = False
    t['package']['autotests'] = False
    t['package']['autobenches'] = False

    lib = t.setdefault('lib', {})
    lib_path = lib.setdefault('path', 'src/lib.rs')
    lib['path'] = os.path.join(rel_path, lib_path)

    bins = t.setdefault('bin', [])
    microram_bins = set(meta.get('bins', ()))
    discard_bins = []
    for i, b in enumerate(bins):
        if b['name'] in microram_bins:
            bin_path = b.setdefault('path', 'src/bin/%s.rs' % b['name'])
            b['path'] = os.path.join(rel_path, bin_path)
        else:
            discard_bins.append(i)
    for i in reversed(discard_bins):
        del bins[i]

    os.makedirs(os.path.dirname(out_path), exist_ok=True)
    toml.dump(t, open(out_path, 'w'))


if __name__ == '__main__':
    in_path, out_path = sys.argv[1:]
    convert(in_path, out_path)
