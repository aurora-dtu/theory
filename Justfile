docs:
    DOCGEN_SRC="file" lake -R -Kenv=dev build PGCL:docs
    - rm -rf doc/
    mkdir -p doc/
    cp -r .lake/build/doc/ doc/
    find doc -name "*.hash" -type f -delete
    find doc -name "*.trace" -type f -delete
    # just docs-zip

docs-zip:
    zip -r docs.zip doc

docs-vscode:
    DOCGEN_SRC="vscode" lake -R -Kenv=dev build PGCL:docs
