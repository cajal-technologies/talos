#!/usr/bin/env bash
# Warm a new Codex worktree from the local checkout's existing Lake artifacts.
#
# On APFS, clonefile creates copy-on-write directory trees: the new worktree
# gets an isolated cache immediately, while unchanged artifacts continue to
# share disk blocks with the source checkout. Lake then rebuilds only artifacts
# whose inputs differ at the worktree's selected commit.

set -euo pipefail

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
source_tree="${CODEX_SOURCE_TREE_PATH:-$(cd "${script_dir}/.." && pwd)}"
worktree="${CODEX_WORKTREE_PATH:-$(git -C "${PWD}" rev-parse --show-toplevel)}"

if [[ ! -d "${source_tree}/.git" && ! -f "${source_tree}/.git" ]]; then
    echo "codex-worktree-setup: source checkout is not a Git worktree: ${source_tree}" >&2
    exit 1
fi
if [[ ! -d "${worktree}/.git" && ! -f "${worktree}/.git" ]]; then
    echo "codex-worktree-setup: destination is not a Git worktree: ${worktree}" >&2
    exit 1
fi

clone_tree() {
    local src="$1"
    local dst="$2"

    [[ -d "${src}" ]] || return 0

    # A cancelled Lake command can leave an empty directory behind. It is safe
    # to remove that exact empty destination and retry the seed.
    if [[ -d "${dst}" && ! -L "${dst}" ]] &&
        ! find "${dst}" -mindepth 1 -print -quit | grep -q .; then
        rmdir "${dst}"
    fi
    if [[ -e "${dst}" || -L "${dst}" ]]; then
        echo "  keep  ${dst#${worktree}/}"
        return 0
    fi

    mkdir -p "$(dirname "${dst}")"

    if [[ "$(uname -s)" == "Darwin" ]]; then
        # clonefile(2) recursively clones a directory on APFS without copying
        # its data blocks. Calling it once also avoids a slow user-space walk.
        /usr/bin/python3 - "${src}" "${dst}" <<'PY'
import ctypes
import os
import sys

libc = ctypes.CDLL("/usr/lib/libc.dylib", use_errno=True)
libc.clonefile.argtypes = [ctypes.c_char_p, ctypes.c_char_p, ctypes.c_uint32]
libc.clonefile.restype = ctypes.c_int

src = os.fsencode(sys.argv[1])
dst = os.fsencode(sys.argv[2])
if libc.clonefile(src, dst, 0) != 0:
    error = ctypes.get_errno()
    raise OSError(error, os.strerror(error), sys.argv[1], sys.argv[2])
PY
    elif cp --help 2>/dev/null | grep -q -- '--reflink'; then
        cp -a --reflink=auto "${src}" "${dst}"
    else
        # Portable fallback for non-APFS filesystems. This is a real copy, but
        # still avoids recompilation and preserves worktree isolation.
        cp -R -p "${src}" "${dst}"
    fi

    seeded_artifacts=true
    echo "  clone ${dst#${worktree}/}"
}

seeded_artifacts=false
dependency_manifests_differ=false
for manifest in \
    interpreter/lake-manifest.json \
    codelib/lake-manifest.json \
    programs/lean/lake-manifest.json; do
    if ! cmp -s "${source_tree}/${manifest}" "${worktree}/${manifest}"; then
        dependency_manifests_differ=true
        break
    fi
done

if [[ "${source_tree}" != "${worktree}" ]]; then
    echo "Seeding Lake artifacts from ${source_tree}"

    # Third-party sources and their cached oleans (Mathlib, Iris, and transitives).
    clone_tree "${source_tree}/.lake/packages" "${worktree}/.lake/packages"

    # Project-owned Lake artifacts. Keep these worktree-local so simultaneous
    # builds cannot overwrite one another.
    package_dirs=(
        interpreter
        codelib
        programs/lean
        verifier
    )
    for package_dir in "${package_dirs[@]}"; do
        clone_tree \
            "${source_tree}/${package_dir}/.lake/build" \
            "${worktree}/${package_dir}/.lake/build"
        clone_tree \
            "${source_tree}/${package_dir}/.lake/config" \
            "${worktree}/${package_dir}/.lake/config"
    done
else
    echo "Using Lake artifacts from the local checkout."
fi

if ! command -v lake >/dev/null 2>&1; then
    echo "codex-worktree-setup: 'lake' is not on PATH" >&2
    exit 1
fi

if [[ "${seeded_artifacts}" == true && "${dependency_manifests_differ}" == true ]]; then
    echo "Dependency revisions differ; fetching their matching binary cache..."
    lake -d "${worktree}/programs/lean" update
    lake -d "${worktree}/programs/lean" exe cache get
fi

echo "Reconciling the cloned artifacts with this worktree..."
lake -d "${worktree}/programs/lean" build
