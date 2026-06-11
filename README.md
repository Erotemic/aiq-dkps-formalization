# AIQ DKPS Formalization

Lean 4 formalizations for response-based embeddings of black-box generative
models, centered on the data kernel perspective space (DKPS) and the
multidimensional-scaling / spectral-perturbation infrastructure needed to make
those theorem statements precise.

This repository focuses on five active Lean libraries:

| Library        | Role                                                                                                                    |
| -------------- | ------------------------------------------------------------------------------------------------------------------------|
| `ForMathlib`   | Mathlib-staging library: paper-agnostic results restated in Mathlib idiom/generality, one file per target Mathlib path. |
| `Acharyya2024` | Asymptotic DKPS/raw-stress MDS consistency for model representations.                                                   |
| `Acharyya2025` | Finite-sample concentration for response-based vector embeddings, including a proved CMDS spectral perturbation bridge. |
| `DkpsQuench`   | Query-efficiency theorem layer for DKPS-based benchmark prediction from cached responses.                               |
| `Helm2025`     | Transfer of statistical-inference guarantees from population DKPS embeddings to estimated/aligned embeddings.           |

The active libraries formalize more than paper-facing wrappers.  They include
supporting mathematics for raw-stress multidimensional scaling, classical MDS
double-centering, finite-dimensional spectral perturbation, Procrustes/alignment
bookkeeping, sample-mean concentration, high-probability event propagation, and
consistency transfer.

## Repository layout

```text
.
├── ForMathlib.lean        # root module for the Mathlib-staging library
├── ForMathlib/            # staged Mathlib additions (see ForMathlib/README.md)
├── Acharyya2024.lean      # root module for the 2024 consistency library
├── Acharyya2024/          # raw-stress MDS, probability, second moments, paper-facing consistency
├── Acharyya2025.lean      # root module for the 2025 concentration library
├── Acharyya2025/          # CMDS, Weyl/Davis-Kahan/Procrustes, aligned finite-sample rates
├── DkpsQuench.lean        # root module for the cached-response query-efficiency layer
├── DkpsQuench/            # theorem statements plus bridge from Acharyya2025 concentration
├── Helm2025.lean          # root module for the statistical-inference transfer layer
├── Helm2025/              # population/estimated DKPS transfer theorem statements and bridge
├── planning/              # current polishing notes and Mathlib-extraction candidates
├── lakefile.toml          # Lake workspace for the four active libraries
├── lake-manifest.json     # pinned dependency manifest
└── lean-toolchain         # Lean toolchain pin
```

The sidecar files such as `Acharyya2025.lean` are normal Lean root modules.  The
subdirectory files are imported as submodules, for example
`Acharyya2025.RateChain`.

## Fresh environment

In a fresh environment you will need to setup Lean4, see:

```bash
./setup_lean.sh
```

## Build

```bash
lake exe cache get
lake build ForMathlib Acharyya2024 Acharyya2025 DkpsQuench Helm2025
```

To build everything declared in `lakefile.toml`:

```bash
lake build
```

## Formalization scope

### `ForMathlib`

Staging area for upstream Mathlib contributions extracted from the paper
libraries: results are restated in Mathlib idiom (e.g. generalized from `ℝ` to
`RCLike 𝕜`), placed in files mirroring their proposed Mathlib destination
paths, and import only Mathlib.  The paper libraries import these general
versions and keep only thin paper-facing specializations.  See
`ForMathlib/README.md` for the contribution workflow and
`planning/mathlib-candidates.md` for the ranked candidate list.

### `Acharyya2024`

Formalizes the consistency layer for generative-model representations in DKPS.
The library includes finite-dimensional DKPS/MDS definitions, second-moment
sample-mean algebra, probability bounds via Chebyshev and union bounds,
raw-stress stability, and repaired paper-facing consistency statements with
explicit hypotheses for uniqueness and sampling/limit behavior.

### `Acharyya2025`

Formalizes a finite-sample concentration chain for response-based vector
embeddings.  Beyond the probability step, this library proves an aligned
classical-MDS perturbation pipeline: double-centering stability,
entrywise-to-operator transport, Weyl-style spectral perturbation,
Davis-Kahan-style subspace control, Procrustes/Gram realization facts,
quantitative polar alignment, and an explicit end-to-end rate chain.

### `DkpsQuench`

Formalizes the conditional query-efficiency theorem layer for benchmark-score
prediction from cached model responses.  The bridge file connects the
finite-configuration concentration result from `Acharyya2025` to the uniform
embedding-error hypotheses used by the query-efficiency argument.

### `Helm2025`

Formalizes transfer results for statistical inference on black-box generative
models in DKPS.  The bridge file connects `Acharyya2025` aligned finite-sample
concentration to estimated-embedding alignment events and consistency
hypotheses used by the inference layer.

## References

### Direct theorem targets

- Aranyak Acharyya, Michael W. Trosset, Carey E. Priebe, and Hayden S. Helm.
  *Consistent estimation of generative model representations in the data kernel
  perspective space*. arXiv:2409.17308, 2024.

- Aranyak Acharyya, Joshua Agterberg, Youngser Park, and Carey E. Priebe.
  *Concentration bounds on response-based vector embeddings of black-box
  generative models*. arXiv:2511.08307, 2025.

- Hayden S. Helm, Aranyak Acharyya, Youngser Park, Brandon Duderstadt, and
  Carey E. Priebe. *Statistical inference on black-box generative models in the
  data kernel perspective space*. Findings of ACL, 2025.

- Hayden Helm, Ben Johnson, and Carey Priebe. *Query-efficient model evaluation
  using cached responses*. arXiv:2605.07096, 2026.

### DKPS and response-based model embeddings

- Brandon Duderstadt, Hayden S. Helm, and Carey E. Priebe. *Comparing
  Foundation Models using Data Kernels*. arXiv:2305.05126, 2023.

- Hayden Helm, Brandon Duderstadt, Youngser Park, and Carey Priebe. *Tracking
  the perspectives of interacting language models*. EMNLP, 2024.

### Multidimensional scaling and alignment

- Warren S. Torgerson. *Multidimensional Scaling: I. Theory and Method*.
  Psychometrika, 17(4):401-419, 1952.

- J. C. Gower. *Some Distance Properties of Latent Root and Vector Methods Used
  in Multivariate Analysis*. Biometrika, 53(3-4):325-338, 1966.

- J. B. Kruskal. *Multidimensional scaling by optimizing goodness of fit to a
  nonmetric hypothesis*. Psychometrika, 29:1-27, 1964.

- Michael W. Trosset and Carey E. Priebe. *Continuous Multidimensional
  Scaling*. arXiv:2402.04436, 2024.

- Anna Little, Yuying Xie, and Qiang Sun. *An Analysis of Classical
  Multidimensional Scaling with Applications to Clustering*. Information and
  Inference: A Journal of the IMA, 12(1):72-112, 2023.

- Colin Goodall. *Procrustes Methods in the Statistical Analysis of Shape*.
  Journal of the Royal Statistical Society, Series B, 53(2):285-321, 1991.

### Spectral perturbation

- Chandler Davis and W. M. Kahan. *The Rotation of Eigenvectors by a
  Perturbation. III*. SIAM Journal on Numerical Analysis, 7(1):1-46, 1970.

- Yi Yu, Tengyao Wang, and Richard J. Samworth. *A useful variant of the
  Davis-Kahan theorem for statisticians*. Biometrika, 102(2):315-323, 2015.

- Yuxin Chen, Yuejie Chi, Jianqing Fan, and Cong Ma. *Spectral Methods for Data
  Science: A Statistical Perspective*. Foundations and Trends in Machine
  Learning, 14(5):566-806, 2021.
