#!/bin/bash
#
# Quick script to install creduce and minimize rb_type_invariant.rs
#

set -e

echo "═══════════════════════════════════════════════════════════════"
echo "  Verus Code Minimizer - rb_type_invariant.rs"
echo "═══════════════════════════════════════════════════════════════"
echo ""

# Check if creduce is installed
if ! command -v creduce &> /dev/null; then
    echo "Installing creduce..."
    sudo apt-get install -y creduce
    echo "✓ creduce installed"
else
    echo "✓ creduce already installed"
fi

echo ""
echo "Starting minimization..."
echo "  Input: rb_type_invariant.rs (492 lines)"
echo "  Script: verified_with_invariant.sh"
echo "  Cores: 8"
echo ""
echo "This will take approximately 20-40 minutes."
echo "You can press Ctrl+C to stop at any time."
echo "The current progress is saved in foo.rs"
echo ""
read -p "Press Enter to continue or Ctrl+C to cancel..."

cd "$(dirname "${BASH_SOURCE[0]}")"
./minimize.sh rb_type_invariant.rs invariant 8


