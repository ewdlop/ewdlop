#!/bin/bash

# Proof Verification Script for nLab Coq Library
# This script systematically verifies all proofs in the library

echo "=========================================="
echo "nLab Coq Library Proof Verification"
echo "=========================================="
echo

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Counters
TOTAL_FILES=0
VERIFIED_FILES=0
FAILED_FILES=0

# Function to verify a single Coq file
verify_file() {
    local file=$1
    echo -n "Verifying $file... "
    
    if coqc -R . nlab "$file" >/dev/null 2>&1; then
        echo -e "${GREEN}✓ VERIFIED${NC}"
        ((VERIFIED_FILES++))
        return 0
    else
        echo -e "${RED}✗ FAILED${NC}"
        echo -e "${YELLOW}Error details:${NC}"
        coqc -R . nlab "$file" 2>&1 | head -5
        echo
        ((FAILED_FILES++))
        return 1
    fi
}

# Function to verify all files in the _CoqProject
verify_all() {
    echo -e "${BLUE}Starting systematic proof verification...${NC}"
    echo

    # Read files from _CoqProject, excluding comments and flags
    while IFS= read -r line; do
        # Skip empty lines, comments, and arguments
        if [[ -z "$line" || "$line" =~ ^# || "$line" =~ ^-.*$ ]]; then
            continue
        fi
        
        # Skip if file doesn't exist or is commented out
        if [[ ! -f "$line" ]]; then
            continue
        fi
        
        ((TOTAL_FILES++))
        verify_file "$line"
        
    done < _CoqProject
}

# Function to generate verification report
generate_report() {
    echo
    echo "=========================================="
    echo -e "${BLUE}PROOF VERIFICATION REPORT${NC}"
    echo "=========================================="
    echo "Total files processed: $TOTAL_FILES"
    echo -e "Successfully verified: ${GREEN}$VERIFIED_FILES${NC}"
    echo -e "Failed verification: ${RED}$FAILED_FILES${NC}"
    
    if [ $FAILED_FILES -eq 0 ]; then
        echo -e "${GREEN}🎉 ALL PROOFS VERIFIED SUCCESSFULLY! 🎉${NC}"
        exit 0
    else
        echo -e "${RED}❌ Some proofs failed verification${NC}"
        exit 1
    fi
}

# Main verification process
main() {
    # Check if we're in the right directory
    if [[ ! -f "_CoqProject" ]]; then
        echo -e "${RED}Error: _CoqProject file not found. Please run from project root.${NC}"
        exit 1
    fi

    # Check if Coq is installed
    if ! command -v coqc &> /dev/null; then
        echo -e "${RED}Error: coqc not found. Please install Coq.${NC}"
        exit 1
    fi

    verify_all
    generate_report
}

# Run verification
main "$@"