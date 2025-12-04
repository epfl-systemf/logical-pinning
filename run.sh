#!/usr/bin/env bash

set -euo pipefail

# Functions for colored messages
error() {
    echo -e "\e[31mERROR: $1\e[0m"
    exit 1
}
info() { echo -e "\e[34m$1\e[0m"; }
success() { echo -e "\e[32m$1\e[0m"; }

SWITCH_NAME="lp"
OCAML_VERSION="4.14.2"
COQ_VERSION="8.20.1"
COQ_EQ_VERSION="1.3.1+8.20"

# Check OPAM
command -v opam >/dev/null 2>&1 || error "OPAM is not installed. Please install OPAM first."

info "This artifact depends on Equations, CFML, and TLC."
info "Tested with Coq $COQ_VERSION and OCaml $OCAML_VERSION."

# Update OPAM
info "Updating OPAM..."
opam update || error "Failed to update OPAM."

# Create or reuse OPAM switch
if opam switch list | awk '{print $2}' | grep -q "^$SWITCH_NAME$"; then
    info "OPAM switch '$SWITCH_NAME' already exists. Reusing it."
else
    info "Creating OPAM switch '$SWITCH_NAME' with OCaml $OCAML_VERSION..."
    opam switch create "$SWITCH_NAME" "ocaml-base-compiler.$OCAML_VERSION" || error "Failed to create OPAM switch."
fi

# Set OPAM environment
info "Setting OPAM environment..."
eval "$(opam env --switch="$SWITCH_NAME" --set-switch)" || error "Failed to set OPAM environment."

# Install Coq if needed
if opam list --installed | grep -q "^coq "; then
    info "Coq is already installed. Skipping."
else
    info "Installing Coq $COQ_VERSION..."
    opam pin add -y coq "$COQ_VERSION" || error "Failed to install Coq."
fi

# Install Equations if needed
if opam list --installed | grep -q "^coq-equations "; then
    info "Coq-Equations is already installed. Skipping."
else
    info "Adding coq-released repository..."
    opam repo add coq-released https://coq.inria.fr/opam/released || true
    info "Installing Coq-Equations $COQ_EQ_VERSION..."
    opam pin add -y coq-equations "$COQ_EQ_VERSION" || error "Failed to install Coq-Equations."
fi

opam install -y pprint menhir

# Compile TLC
info "Compiling TLC ..."
make -C lib/tlc -j4 || error "Failed to compile TLC."

# Compile CFML
info "Compiling CFML ..."
make -C lib/cfml depend || error "Failed to compile CFML."
make COQEXTRAFLAGS="-Q ../tlc/src TLC" -C lib/cfml -j libcoq stdlib || error "Failed to compile CFML."

# Compile Logical-Pinning
if [ -f Makefile ]; then
    info "Compiling the artifact..."
    make || error "Compilation failed."
else
    error "Makefile not found. Cannot compile the artifact."
fi

success "Setup completed successfully!"
