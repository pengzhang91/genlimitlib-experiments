# Review-snapshot provenance

The original anonymous review artifact was a fresh, history-free snapshot.
Its published files excluded
source-repository histories, remotes, local editor state, build caches,
credentials, private project links, direct artifact-author identifiers, and
personal absolute paths. The public release now identifies the authors in its
documentation. This public derivative also abbreviates selected reading-input
excerpts as described in PUBLIC_RELEASE.md; saved response evidence is retained.
Historical anonymity reports describe the earlier snapshot, not the current
public documentation.

Public scholarly citations and cited-author names remain in source locators
and mathematical references. They are not
artifact-authorship metadata.

The local Lean build cache under `section4_formalization/GenLimitLean/.lake/`
is excluded by `.gitignore` and must not be force-added or included in a manual
ZIP upload. Use normal Git staging from this repository root so ignored caches,
compiled objects, and `.DS_Store` files remain outside the published artifact.

The anonymous hosting service did not rewrite binary files. PDF metadata,
embedded hyperlinks, ZIP payloads, and compressed experiment inputs were
therefore audited directly before release.
