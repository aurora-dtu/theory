docs:
    DOCGEN_SRC="vscode" lake -R -Kenv=dev build PGCL:docs MDP:docs HeyLo:docs

watch-docs:
    watchexec -e lean just docs

check-docs:
    #!/bin/bash

    GREEN='\033[1;32m'
    RED='\033[1;31m'
    BOLD='\033[1m'
    LIGHT='\033[2m'
    ITALIC='\033[3m'
    NC='\033[0m' # No Color

    total=0
    documented=0

    while IFS= read -r file; do
        total=$((total + 1))
        if grep -q "/-!" "$file"; then
            documented=$((documented + 1))
            echo -e "${GREEN}✔${NC} ${LIGHT}$file${NC}"
        else
            echo -e "${RED}✘${NC} $file"
        fi
    done < <(fd .lean)

    echo -e "${BOLD}[${GREEN}$documented${NC}${BOLD}/${RED}$total${NC}${BOLD}] files documented${NC}"
