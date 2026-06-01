# Artifact for checking translatability of MathLib Theorems regarding a DTT to DHOL translation

## Building

Build the Podman image. This step needs to be performed twice, once on an
X86 machine and once on an ARM64 machine.

```bash
podman build . -t dtt-dhol-artifact
# on x86
podman dtt-dhol-artifact -o out/artifact-x86.tar
# or, on arm64
podman save dtt-dhol-artifact -o out/artifact-arm64.tar
```

Copy all remaining data to `out/`:

```bash
cp README.artifact.md out/README.md
cp results-natural.tar results-synth.tar out/
```

## Acknowledgements

Evaluation setup used is by Jannis Limperg and Xavier Généreux for ["Incremental Forward Reasoning for White-Box Proof Search"](https://github.com/JLimperg/artifact-aesop-forward).
