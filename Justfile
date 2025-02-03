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
    DOCGEN_SRC="vscode" lake -R -Kenv=dev build PGCL:docs MDP:docs

check-docs:
    #!/bin/bash

    GREEN='\033[1;32m'
    RED='\033[1;31m'
    LIGHT='\033[2m'
    NC='\033[0m' # No Color

    fd .lean | while read -r file; do
        if grep -q "/-!" "$file"; then
            echo -e "${GREEN}✔${NC} ${LIGHT}$file${NC}"
        else
            echo -e "${RED}✘${NC} $file"
        fi
    done
