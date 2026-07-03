# List available recipes (default when you just run `just`)
default:
    @just --list

# Check everything (your main command)
build:
    lake build

# Run the executable
run:
    lake exe proofpractice

# Start the Lean server / open project (build first)
check: build

# Update dependencies (rarely needed — only to bump Mathlib)
update:
    lake update
    lake exe cache get

# Refresh the Mathlib binary cache
cache:
    lake exe cache get

# Remove build artifacts
clean:
    lake clean

# Build, then run
all: build run
