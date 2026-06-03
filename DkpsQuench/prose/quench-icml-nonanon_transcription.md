# Query-efficient model evaluation using cached responses

See: https://arxiv.org/abs/2605.07096

Hayden Helm<sup>1</sup>, Ben Johnson<sup>2</sup>, Carey E. Priebe<sup>3</sup>

<sup>1</sup> Helivan. <sup>2</sup> Jataware. <sup>3</sup> Johns Hopkins University. Correspondence to: HH &lt;hayden@helivan.io&gt;.

Preprint. January 28, 2026.

## Abstract

Evaluating a new model on an existing benchmark is often necessary to understand its behavior before deployment. For modern evaluation frameworks, generating and evaluating a response for all queries can be prohibitively expensive. In practice, responses from previously-evaluated models are often cached - creating a potential opportunity to use this additional information to decrease the number of queries required to accurately evaluate a new model. In this paper, we introduce an approach for predicting benchmark performance that leverages cached model responses based on the Data Kernel Perspective Space (DKPS), a method for quantifying the relationship between models in the black-box setting. Theoretically, we show that DKPS-based methods are query-efficient under certain conditions. Empirically, we demonstrate that DKPS-based methods achieve the same mean absolute error as baselines with a substantially decreased query budget. We conclude by proposing an offline method for selecting a set of queries that maximizes the goodness-of-fit on reference models, improving prediction accuracy over random query selection.

## 1. Introduction

Benchmarks for machine learning methods are widely used to measure the field's progress. While they are not without flaw (Recht et al., 2019), the ubiquity and longevity of early benchmarks such as MNIST (LeCun et al., 2010), CIFAR-10 (Krizhevsky, 2009), and the Iris dataset (Fisher, 1936) attest to their practical utility. In the era of modern generative models, benchmarks have shifted away from evaluating performance on a single, well-defined task and moved towards evaluating performance across a suite of tasks designed to capture a model's overall capability. For example, (Liang et al., 2022) introduced the HELM benchmark suite and leaderboard as an attempt to evaluate language models as comprehensively and transparently as possible. Similar multi-task benchmark suites and leaderboards now exist for embedding models (Muennighoff et al., 2023), image generation (Huang et al., 2025), coding (Chen et al., 2021), and "intelligence" (Chollet, 2019), among others.

Although multi-task evaluations offer a more complete picture of a model's strengths and weaknesses, they are often computationally expensive. Evaluating a model on a modern multi-task benchmark typically requires generating and scoring thousands of responses, making full evaluation increasingly impractical as both model sizes and benchmark scopes grow. At the same time, it is easier than ever to produce new model behavior - via parameter efficient fine-tuning (Han et al., 2024), instruction tuning (Zhang et al., 2025), model merging (Matena & Raffel, 2022), distillation (Gou et al., 2021), prompt engineering (Sahoo et al., 2025), etc. - making it infeasible to evaluate each new variant. These trends motivate the need for query-efficient alternatives to full benchmark evaluation. In this paper, we address this problem by leveraging information and responses from previously evaluated models under the assumption that it is possible to predict a new model's score by leveraging the similarity between its responses and cached responses from already-scored models on a (small) subset of queries.

**Contribution.** We make two primary contributions.

1. **Theoretical:** We prove that a benchmark prediction method based on the Data Kernel Perspective Space (DKPS) is query-efficient relative to estimating benchmark performance using a subset of queries.
2. **Empirical:** We validate theoretical query-efficiency of DKPS-based methods. As summarized in Table 1, DKPS-based methods can reduce the number of queries required to achieve a given performance by more than 10x.

### 1.1. Background & related work

**Low-dimensional representations of language models.** Our work contributes to a growing literature on low-dimensional representations of language models. Some approaches construct representations by comparing internal activations across models (Duderstadt et al., 2023; Huh et al., 2024; Horwitz et al., 2025) or by comparing model weights directly (Chen et al., 2025). However, evaluation frameworks typically do not require (or even allow) access to model internals, and instead rely only on model responses. The Data Kernel Perspective Space (DKPS), first introduced in the context of monitoring multi-agent systems (Helm et al., 2024b), addresses this setting by mapping a collection of generative models into a low-dimensional Euclidean space via multidimensional scaling of matrices containing average embedded responses. Recent theoretical work has shown that DKPS recovers ground-truth low-dimensional model structure as the number of models, queries, and responses per query grow (Acharyya et al., 2024; 2025) and that supervised inference methods trained on DKPS representations are consistent (Helm et al., 2025). We frame predicting the score of a model on a benchmark as an instance of model-level inference in the black-box setting and extend recent theoretical and empirical results related to the DKPS to query-efficiency for benchmark score prediction.

**Efficient benchmarking.** Several lines of work aim to reduce the computational cost of benchmark evaluation. Polo et al. (2024) use Item Response Theory to construct benchmark subsets of 100 examples (approx. 1% of original size) that predict performance within 2% error. Vivek et al. (2024) propose clustering examples based on cross-model predictions and selecting cluster centers as "anchor points," achieving accurate rankings with significantly fewer examples. Bean et al. (2025) propose item-centric selection based on cognitive embeddings, improving cold-start performance and cross-family transferability. Li et al. (2024) use reinforcement learning to model dependencies across examples, reducing estimation error by 25-50% via active selection. Perlitz et al. (2024) analyze benchmark design choices and propose ranking algorithms achieving 100x cost reductions with minimal "reliability" loss. These techniques typically require explicit or implicit task-specific structure, model metadata, access to model internals, or a response-level scoring functions.

Our approach is complementary to prior work in that we leverage cached responses from previously evaluated models, operate purely via black-box access and model response similarity, and assume no structure across tasks or subtasks. Importantly, this enables combining our method with existing techniques - e.g., using DKPS-based methods to predict performance on IRT-selected subsets (Polo et al., 2024) or on "anchor points" (Vivek et al., 2024) - to potentially compound efficiency gains beyond what either approach achieves alone.

### 1.2. Problem statement

Given a generative model $f$, we consider the problem of predicting its score on a benchmark $Q^* = \{q_1, \ldots, q_M\}$. Let

$$
y : \mathcal{F} \times 2^{Q^*} \to [0, 1]
$$

denote the benchmark scoring function. That is, $y(f, Q^*)$ is the score assigned to $f$ after evaluating it on all queries. We refer to $y(f, Q^*)$ as $y$ when the context is clear.

As described above, full evaluation of $f$ on all queries may be infeasible. Instead, we assume access to previously-evaluated (model, score) pairs $(f_1, y_1), \ldots, (f_n, y_n)$ and each model's response to each query $\{\{ f_i(q_j) \}_{j=1}^{M}\}_{i=1}^{n}$. Given this additional information, our goal is to estimate $y$ with $m \ll M$ queries. That is, we seek to identify an estimate $\hat{y}$ that predicts the full benchmark score of $f$ from its responses to a subset $Q \in 2^{Q^*}$ of the benchmark queries and the information available from the previously-evaluated models.

## 2. The Data Kernel Perspective Space

For our purposes, a model $f \in \mathcal{F}$ is a random mapping from a query space $\mathcal{Q}$ to a response space $\mathcal{X}$. Given $q \in \mathcal{Q}$, model responses $f(q)_1, \ldots, f(q)_r$ are sampled i.i.d. from the distribution $F$. We let $g : \mathcal{X} \to \mathbb{R}^p$ be a fixed embedding function that maps a response to a real-valued vector.

Given models $f_1, \ldots, f_n$ and queries $Q = \{q_1, \ldots, q_m\}$, we let $\bar{X}_i \in \mathbb{R}^{m \times p}$ be the matrix whose $j$th row is the average embedded response from $f_i$ to query $q_j$; or,

$$
\bar{X}_{ij\cdot} = \frac{1}{r}\sum_{k=1}^{r} g(f_i(q_i))_k.
$$

Further, we let $D$ be the pairwise distance matrix with entries

$$
D_{ii'} = \|\bar{X}_i - \bar{X}_{i'}\|_F.
$$

We refer to the distribution on embedded responses induced by $f_i(q_j)$ as $F_{ij}$.

Following (Acharyya et al., 2024), the $d$-dimensional Data Kernel Perspective Space (DKPS) representations of the models are defined as the vectors $(\hat{\psi}_1, \ldots, \hat{\psi}_n)$ that are a solution to

$$
(\hat{\psi}_1, \ldots, \hat{\psi}_n) = \arg\min_{z_i \in \mathbb{R}^d} \sum_{i,i'}^{n} \left(\|z_i - z_j\| - D_{ii'}\right)^2.
\tag{1}
$$

DKPS enables treating model-level analysis as a problem in a low-dimensional Euclidean space. We note that the solution to Eq. (1) - and the quality of the representations for a given task - may depend on the choice of query set $Q$ and embedding function $g$. When the context is not clear, we emphasize the dependence on $Q$ by referring to $\psi$ as $\psi(Q)$. In the benchmark setting, the choice of $Q$ is reasonably constrained to elements of $2^{Q^*}$. Finally, we let $\hat{\Psi}_Q : \mathcal{F} \to \mathbb{R}^d$ be a mapping from the model space to the estimated perspective space under $Q$; that is $\hat{\Psi}_Q(f_i) = \hat{\psi}_i(Q)$.

Figure 1 shows the $d = 2$ DKPS of models induced by various choices of $n$ and $m$. Each dot is a model colored by score on the counting and probability subtask from HELM-Lite.

> **Figure 1.** Example $d = 2$-dimensional Data Kernel Perspective Spaces (DKPS) for models publicly evaluated on HELM-Lite's MATH counting and probability subtask. Each panel includes the DKPS representations for different $(n, m) =$ (number of models, number of queries) pairs induced by a random query set of size $m$. Each dot is a model colored by its score on the subtask. As the number of queries increases (left to right), the models with similar scores are more tightly clustered. As the number of models increases (top to bottom), there are more models to help localize score signal.

### 2.1. Theoretical properties of the DKPS

For a fixed collection of models, query set, and number of responses, the $d$-dimensional DKPS representations of the models - $\hat{\psi}_1, \ldots, \hat{\psi}_n$ - are estimates of a set of "true" $d$-dimensional vectors $\psi_1, \ldots, \psi_n$. That is, as $n$, $m$, and $r$ tend to infinity at particular relative rates, $\lim \hat{\psi}_i \to \psi_i$ (Acharyya et al., 2024). Further, the error of the worst estimate is bounded above by a constant dependent on the number of models, the number of queries, the number of replicates, and the DKPS dimension:

$$
\max_i \|\hat{\psi}_i - \psi_i\|_2 \le c(n, m, r, d)
$$

with high probability (Acharyya et al., 2025). Given its importance to provable query-efficiency, we state this last result in its entirety here:

**Theorem 1.** [Acharyya et al. (2025) Theorem 2] In our setting, suppose $r = \omega(n^3)$ and $\sup_{ij} \operatorname{trace}(\operatorname{Cov}(F_{ij})) = O(1)$. Then, under technical assumptions, for every $\delta \in (0, 1/2)$ and for sufficiently large $n$ and $r$

$$
\max_i \|\hat{\psi}_i - \psi_i\|_2 \le \operatorname{Poly}_3\left(\left(\frac{n^3}{r}\right)^{\frac{1}{2} - \delta}\right)
$$

with high probability, where $\operatorname{Poly}_3(x)$ is a third degree polynomial in $x$.

The concentration result of Theorem 1 is necessary to make claims related to the quality of representations for a given $(n, m, r)$, which is critical for analyzing the query efficiency of DKPS-based methods for benchmark score prediction.

### 2.2. Inference in the DKPS

Following Helm et al. (2025), we consider model-level inference in DKPS as a statistical problem: Let $(f,y), (f_1,y_1), \ldots, (f_n,y_n)$ be i.i.d. samples from a joint distribution on (model, score) pairs. In the benchmark prediction setting, given $f$ the true benchmark score $y$ is deterministic and analysis with the marginal distribution on $f$ is equivalent to analysis with the joint distribution. We refer to the distribution on models as $P_f$.

Our goal is to construct a decision function $h : \mathcal{F} \to \mathcal{Y}$ that minimizes the expected loss over $P_f$. In practice, operating directly on the space of models is too complex. Instead, we consider the proxy problem of model-level inference in DKPS: we observe perspective-score pairs $(\hat{\Psi}_Q(f), y), (\hat{\Psi}_Q(f_1), y_1), \ldots, (\hat{\Psi}_Q(f_n), y_n)$ and use these to construct a decision function $h_n^Q : \mathcal{F} \to \mathcal{Y}$ defined by

$$
h_n^Q(f) = \hat{h}_n^Q(\hat{\Psi}_Q(f))
$$

where $\hat{h}_n^Q : \mathbb{R}^d \to \mathcal{Y}$ is trained on $\{(\hat{\Psi}_Q(f_i), y_i)\}_{i=1}^{n}$. Formally, with loss function $\ell : \mathcal{Y} \times \mathcal{Y} \to \mathbb{R}$, our goal is to select $\hat{h}_n^Q$ to minimize

$$
\mathbb{E}_{P_f}\left[\ell(h_n^Q(f), y)\right]
= \mathbb{E}_{P_f}\left[\ell(\hat{h}_n^Q(\hat{\Psi}_Q(f)), y)\right].
$$

We sometimes refer to $h_n^Q$ as $h_n^{(m)}$ as context requires.

## 3. Provable query-efficiency in the DKPS

In this section we define query-efficiency and prove that a simple regression function on the perspectives is query-efficient relative to estimating the model's score with its score on a subset of the benchmark queries. Recall $y := y(f,Q^*)$.

For a fixed $Q \subseteq Q^*$ with $|Q| = m$, we say the sequence of decision functions $(h_1^Q, h_2^Q, \ldots)$ is $Q$ query-efficient relative to $(h_1'{}^Q, h_2'{}^Q, \ldots)$ if there exists $N \in \mathbb{N}$ such that

$$
\mathbb{E}_{P_f}\left[\ell\left(h_n^Q(f), y\right)\right]
\le
\mathbb{E}_{P_f}\left[\ell\left(h_n'{}^Q(f), y\right)\right]
\tag{2}
$$

for all $n > N$. We say the sequence of decision functions $(h_1^{(m)}, \ldots, h_n^{(m)})$ is $m$ query-efficient relative to $(h_1'{}^{(m)}, \ldots, h_n'{}^{(m)})$ if for all $Q$ with $|Q| = m$ there exists $N_Q \in \mathbb{N}$ such that Eq. (2) holds for all $n > N_Q$.

Finally, we say the sequence of decision functions $(h_1^{(m)}, \ldots, h_n^{(m)})$ is query-efficient relative to $(h_1'{}^{(m)}, \ldots, h_n'{}^{(m)})$ if for all $m < M$ there exists $N^{(m)} \in \mathbb{N}$ such that it is $m$-query efficient.

For our theoretical analysis we assume the benchmark score function is well-defined on all subsets of $Q^*$. For $Q \subset Q$, we let $\hat{y}_Q := y(f,Q)$.

Let $h_n^{(m)}$ be nearest neighbor regression in perspective space and $\delta^* = \min_i \|\hat{\psi}_i - \hat{\psi}\|_F$:

$$
\hat{y}_{NN} := h_n^{(m)}(\hat{\psi}) =
\frac{\sum_{i=1}^{n} \mathbf{1}\{i : \|\hat{\psi}_i - \hat{\psi}\|_F = \delta^*\}y_i}
{\sum_{i=1}^{n} \mathbf{1}\{i : \|\hat{\psi}_i - \hat{\psi}\|_F = \delta^*\}}.
$$

To establish query-efficiency of nearest neighbor regression in DKPS, we require two key assumptions.

**Assumption 1 (Lipschitz Score Function).** Given $Q \subseteq 2^{Q^*}$, the benchmark score function $y(\cdot,Q^*) : \mathcal{F} \to \mathbb{R}$ is $\gamma$-Lipschitz on the perspective space induced by $Q$; or, there exists $\gamma > 0$ such that for any $f, f' \in \mathcal{F}$,

$$
|y(f,Q^*) - y(f',Q^*)| \le \gamma \cdot \|\psi(Q) - \psi'(Q)\|_2.
$$

The smoothness on the mapping from $y$ to $\psi(Q)$ ensures that nearby models in DKPS have similar benchmark scores. In practice, when $m = M$ Assumption 1 will hold if the embedding function $g$ is sufficiently smooth with respect to $y$. With the same condition on $g$, Assumption 1 will hold in practice for $m < M$ in a probabilistic sense.

**Assumption 2 (Model Distribution Support).** The model distribution $P_f$ has non-zero measure on all compact subsets of $\mathcal{F}$. Equivalently, for any target model $f$ and radius $\delta > 0$, there exists $\epsilon > 0$ such that

$$
P_f(B_\delta(f)) \ge \epsilon
$$

where $B_\delta(f) = \{f' \in \mathcal{F} : d_F(f,f') < \delta\}$ for some appropriately defined $d_F$.

Denseness on the space of models ensures that as $n$ increases, we observe models close to any target model with high probability. In practice, Assumption 2 suggests that a large, diverse set of reference models may be needed to realize query efficiency for an arbitrary target model.

Given Assumptions 1 & 2 we are able to arbitrarily bound the prediction error of nearest neighbor regression as a function of $(n,m,r)$. We now state our main theoretical result:

**Theorem 2.** For any $\epsilon > 0$ there exists $(n,m,r)$ such that

$$
MSE(\hat{y}_{NN}) \le \epsilon
$$

with high probability. That is, for $m < M$ such that $MSE(\hat{y}_Q) > 0$, $\hat{y}_{NN}$ is query-efficient relative to $\hat{y}_Q$ with high probability.

We provide the proof of Theorem 2 in its entirety.

**Proof.** Fix $Q \subseteq Q^*$. Let $f$ be a target model with true perspective $\psi$ and estimated perspective $\hat{\psi}$, and let $f^* \in \arg\min_i \|\hat{\psi}_i - \hat{\psi}\|_2$ denote one of its nearest neighbors with perspectives $\psi^*$ and $\hat{\psi}^*$. The prediction error is

$$
|\hat{y}_{NN} - y| = |y(f^*,Q^*) - y(f,Q^*)|.
$$

By Assumption 1, we have

$$
|y(f^*,Q^*) - y(f,Q^*)| \le \gamma \cdot \|\psi^* - \psi\|_2.
$$

By the triangle inequality:

$$
\|\psi^* - \psi\|_2 \le \|\psi^* - \hat{\psi}^*\|_2 + \|\hat{\psi}^* - \hat{\psi}\|_2 + \|\hat{\psi} - \psi\|_2.
$$

Let $\delta^* = \|\hat{\psi}^* - \hat{\psi}\|_2$ and let $c = c(n,m,r,d)$ be the concentration bound from Theorem 1. With high probability, $\max_i \|\hat{\psi}_i - \psi_i\|_2 \le c$, so $\|\psi^* - \psi\|_2 \le 2c + \delta^*$. Thus

$$
|y^* - y| \le \gamma(2c + \delta^*).
$$

By Theorem 1, for $r = \omega(n^3)$ and sufficiently large $n$ and $r$, the constant

$$
c \le \operatorname{Poly}_3\left((n^3/r)^{1/2 - \delta}\right)
$$

can be made arbitrarily small.

By Assumption 2, for any $\epsilon' > 0$, there exists $n_0$ such that for $n > n_0$,

$$
P_f\left(\min_i \|\psi_i - \psi\|_2 < \epsilon'\right) \ge 1 - \eta
$$

for arbitrarily small $\eta > 0$. Combined with the concentration result, $\delta^* < \epsilon' + 2c$ with high probability.

Therefore, with high probability:

$$
|y^* - y| \le \gamma(2c + \delta^*) < \gamma(4c + \epsilon').
$$

For any $\epsilon > 0$, choose $c < \epsilon^{1/2}/(8\gamma)$ and $\epsilon' = \epsilon^{1/2}/(2\gamma)$ with $n$ and $r$ sufficiently large. Then with high probability,

$$
|y^* - y| < \gamma \cdot \epsilon^{1/2}/\gamma = \epsilon^{1/2},
$$

so

$$
MSE(\hat{y}_{NN}) = \mathbb{E}_{P_f}\left[(y^* - y)^2\right] \le \epsilon
$$

with high probability.

Thus, if $MSE(\hat{y}_Q) > 0$ then there exists $N$ such that for $n > N$, $MSE(\hat{y}_{NN}) < MSE(\hat{y}_Q)$, establishing query-efficiency. $\square$

That is, benchmark score prediction using the geometry induced by DKPS using a sufficiently large number of models and cached responses to a subset of benchmark queries is better than using a model's score on the subset of queries.

## 4. Empirical query-efficiency in the DKPS

We next provide empirical evidence that DKPS-based prediction methods are query-efficient.

### 4.1. Evaluation set up

**Benchmarks.** We evaluate DKPS-based prediction methods on tasks from the HELM-Lite benchmark suite (Liang et al., 2022). Specifically, we consider four tasks: MATH (Hendrycks et al., 2021), which includes 7 subject-based subtasks; LegalBench (Guha et al., 2023), which includes 11 legal reasoning subtasks; MedQA (Jin et al., 2020), a multiple-choice medical exam dataset; and WMT-14 (Bojar et al., 2014), which includes 6 language-pair translation subtasks. Each task employs a different response-level scoring function, $s : Q^* \to [0,1]$: correctness for MATH, quasi exact match for LegalBench and MedQA, and BLEU score for WMT-14.

For our purposes, the score for a given subtask is the average response-level score across all queries in that task. The score for a given task is the average subtask score. Full evaluation requires 437 responses for MATH, 2047 responses for LegalBench, 1000 responses for MedQA, 678 responses for WMT-14.

**Models.** We evaluate models from the HELM-Lite leaderboard that have been scored on each respective task. Because models are evaluated asynchronously and the benchmark evolves over time, different tasks have different sets of evaluated models. Critically, our method requires that all models be evaluated on the same set of queries (to construct the distance matrix $D$), so we restrict our analysis to maximal subsets of models sharing a common query set within each subtask and task. The task with the fewest evaluated models is LegalBench (93 models). The median and max number of models evaluated on a given task is 95. In total, 95 unique models appear across all tasks. Table 2 in the Appendix lists all models included in at least one evaluation, and Table 3 in the Appendix indicates which models were not evaluated on which tasks.

To ensure our evaluation reflects genuine predictive performance, we adopt a "Leave-One-Family-Out" (LOFO) evaluation protocol. Models are grouped into families based on their base architecture and training procedure (e.g., all Llama variants form one family; see Table 2 for complete groupings). For each evaluation run, we:

1. Select a held-out model family as the prediction target.
2. Sample $n$ reference models from the remaining families.
3. Sample a query subset $Q$ of size $m$ from the benchmark.
4. Construct $d$-dimensional DKPS representations for the reference models and the held-out model family using their responses to $Q$.
5. Train a decision function $\hat{h}_n$ on $\{(\hat{\psi}_i, y_i)\}$ for the $n$ reference models to make prediction $\hat{y} = h_n^{(m)}(\hat{\psi})$.
6. Predict scores for all models in the held-out family.

We repeat this protocol 1024 times for each combination of $(n,m)$ and report the mean absolute error (MAE) averaged across all held-out models. The LOFO protocol ensures that predictions do not rely on model family artifacts. As such, our results provide a conservative estimate of real-world query-efficiency.

**Embedding function & DKPS configuration.** We map model responses to vector representations using task-appropriate embedding functions. Unless stated otherwise, for free-form text responses (MATH, WMT-14) we use the sentence embedding model `gemini-embedding-001`, which produces one 3024-dimensional vector per response. For multiple-choice responses (MedQA, LegalBench), we use one-hot encodings in $\mathbb{R}^p$, where $p$ is the number of answer choices.

While the DKPS framework supports multiple responses per query, HELM-Lite requires only a single response per model-query pair, so $r = 1$ throughout.<sup>1</sup> We assume the pairwise distance matrix $D$ is a Euclidean distance matrix and hence solve Eq. (1) with GraSPy's (Chung et al., 2019) implementation of classical multi-dimensional scaling (Torgerson, 1952). We fix $d = 8$ for consistency across experiments, though adaptive methods such as selecting $d$ based on the elbows in the scree plot (Zhu & Ghodsi, 2006) for each task or subtask may yield further improvements.

<sup>1</sup> For the majority of the publicly evaluated models available on HELM, they were evaluated with a temperature of 0; that is, $E(f(q)) = f(q)$ and so $r > 1$ is not necessary.

**Prediction methods.** We compare four prediction methods: two baselines that do not use DKPS representations, and two DKPS-based approaches.

- **Population Mean:** Predicts the benchmark score as the average score of the $n$ reference models:

  $$
  \hat{y} = \frac{1}{n}\sum_{i=1}^{n} y_i.
  $$

  This baseline ignores both the target model's responses and the query subset.

- **Sample Score:** Predicts the benchmark score using the target model's average response-level score on the query subset $Q$:

  $$
  \hat{y}_{sample} = \frac{1}{m}\sum_{q \in Q} s(f(q)).
  $$

  When $m = M$, this recovers the true benchmark score. This baseline uses the target model's responses but ignores information from reference models.

- **DKPS:** Trains a linear regressor on the DKPS representations of the $n$ reference models to predict benchmark scores:

  $$
  \hat{y}_{DKPS} = \beta_0 + \beta_1^{\top}\hat{\psi},
  $$

  where $(\beta_0, \beta_1)$ are learned via ordinary least squares on $\{(\hat{\psi}_i, y_i)\}_{i=1}^{n}$. This method leverages cross-model structure but does not directly use response-level scores. We sometimes evaluate various choices of $n$.

- **Ensemble:** Convex combination of Sample Score and DKPS predictions:

  $$
  \hat{y}_{ensemble} = \alpha \cdot \hat{y}_{sample} + (1 - \alpha) \cdot \hat{y}_{DKPS}.
  $$

  In our experiments, we set $\alpha = m/M$. This weighting reflects our confidence in the sample-based estimate: when $m$ is small, we rely more on DKPS; when $m \approx M$, we rely more on the direct sample score.

All predictions are clipped to $[0,1]$. We use ordinary least squares for the DKPS regressor due to its strong empirical performance when testing. Alternatives such as kernel regression or locally weighted regression may further improve performance and are required for the theoretical query-efficiency guarantees in Section 3. We leave exploration of these methods to future work.

### 4.2. Results

**DKPS-based methods outperform Sample Score at low query budgets.** Figure 2 shows the MAE for each of the prediction methods for the representative subtasks. For $m$ small, DKPS-based methods outperform Sample Score across all subtasks and all number of reference models. Importantly, for $n = ALL$, the earliest intersection between the performance of $y_{DKPS}$ and $y_{SS}$ is $m \approx 10$ (for MATH's counting and probability). For the other three subtasks, however, the region in which $y_{DKPS}$ outperforms $y_{NN}$ is even more substantial - the performances of the two methods intersect beyond $m = 30$.

The more reference models that are included, the better the DKPS-based methods perform. The effect of adding more reference models depends on the task. As hinted by Assumption 2, it is possible that including more reference models would meaningfully shift the point where the performances intersect.

Table 1 shows performance of the methods as a function of query budget $m$ for the full tasks from HELM-Lite. We observe similar relative performance at the task level as we do at the subtask level.

**Table 1.** Mean absolute error (MAE) of benchmark prediction methods under varying query budgets for four HELM-Lite tasks. Results averaged over 1024 random query subsets of size $m$ using all available reference models for DKPS and Ensemble. Evaluation is under the Leave-One-Family-Out protocol. Lower is better; bold indicates lowest MAE per (task, $m$) pair. DKPS-based methods consistently outperform baselines at low query budgets, achieving comparable accuracy with substantially fewer queries (e.g., on legalbench, DKPS at $m = 1$ achieves MAE approx. Sample Score at $m = 16$, a 16x reduction).

| Method | legalbench m=1 | legalbench m=4 | legalbench m=16 | legalbench m=64 | medqa m=1 | medqa m=4 | medqa m=16 | medqa m=64 | wmt_14 m=1 | wmt_14 m=4 | wmt_14 m=16 | wmt_14 m=64 | math m=1 | math m=4 | math m=16 | math m=64 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| Pop. Mean | 0.093 | 0.093 | 0.093 | 0.093 | 0.131 | 0.131 | 0.131 | 0.131 | 0.048 | 0.048 | 0.048 | 0.048 | 0.234 | 0.234 | 0.234 | 0.234 |
| Sample Score | 0.472 | 0.199 | 0.097 | 0.048 | 0.420 | 0.189 | 0.093 | 0.044 | 0.153 | 0.073 | 0.037 | 0.017 | 0.339 | 0.163 | 0.079 | 0.037 |
| DKPS | **0.087** | **0.067** | 0.051 | 0.034 | **0.121** | **0.094** | 0.066 | 0.039 | **0.038** | **0.026** | 0.019 | 0.016 | 0.144 | 0.105 | 0.082 | 0.070 |
| Ensemble | **0.087** | **0.067** | **0.049** | **0.033** | **0.121** | **0.094** | **0.065** | **0.038** | **0.038** | **0.026** | **0.018** | **0.013** | **0.143** | **0.104** | **0.074** | 0.042 |

> **Figure 2.** Regression in the Data Kernel Perspective Space (DKPS) provides query-efficient benchmark prediction relative to using the sample score across the representative HELM-Lite subtasks. Lines represent the average mean absolute error across leave-one-family-out and 512 randomly sampled query sets. Lower is better. Actual query-efficiency depends on the number of models used to induce DKPS and train the regression function, as well as the task. The ensemble regressor dominates for nearly all number of queries and all tasks.

**Ensemble method dominates across all query budgets.** While DKPS and Sample Score each excel in different number of query regimes, the Ensemble method achieves the best performance across nearly all $(m, task)$ combinations, often outperforming both components and the Population Mean baseline. The ensemble's adaptive weighting ($\alpha = m/M$) is effective: at small $m$, it inherits DKPS's ability to exploit cross-model structure; at large $m$, it transitions to rely on the target model's actual response-level scores. This result has important implications. In particular, practitioners need not choose between methods. In some cases where cross-task structure can be assumed, more adaptive weightings may provide additional efficiency (Helm et al., 2024a) - though the proposed weighting appears sufficient for out-of-the-box use.

**Embedding function choice can have non-negligible effect.** The preceding results used `gemini-embedding-001` to map responses to vectors. Figure 3 examines whether this choice matters by comparing six embedding functions on the Math (counting and probability) subtask. At small $m$, embedding choice has a meaningful effect: the best-performing embedding (`gemini-embedding-001`) achieves roughly 20% lower MAE than the worst (`all-minilm-l6-v2`) at $m = 1$. This gap narrows as query budget increases, and by $m \ge 30$ all embeddings perform comparably.

Notably, embedding capacity does not predict performance. Larger models do not uniformly outperform smaller ones, suggesting that alignment between the embedding space and task structure may matter more than raw dimensionality. For practitioners, we recommend selecting an embedding function carefully when operating at low query budgets: a 2-3% reduction in MAE can translate to significant cumulative savings when evaluating new model variants.

> **Figure 3.** Choice of embedding function can have a large effect at small $m$. For small $m$, the best performing embedding model (`gemini-embedding-001`) improves upon the worst performing (`all-minilm-l6-v2`) by approx. 20% (from MAE approx. 0.15 to MAE approx. 0.12) at $m = 1$. For large enough $m$, any modern sentence embedding function is sufficient.

**Model-level performance reveals broad applicability.** The top row of Figure 4 shows the distribution of performance gain from using Ensemble (relative to Sample Score) at the individual model level. A dot above 0 indicates that using the ensemble improve benchmark estimation for that model. As can be seen in the figure, the majority of the mass of each distribution is above 0 for all $m$ and all subtasks. At low query budgets, the distributions are heavily concentrated above zero across all tasks. This observation indicates that combining DKPS-based prediction with sample scores benefits diverse model types, even with LOFO protocol.

However, the variance in these benefits differs substantially across tasks. WMT exhibits remarkably low spread, with models clustering tightly around the mean, suggesting the Ensemble's adaptive weighting provides uniform improvements for this task. In contrast, MedQA and Math the performance differences have wider distributions - some models gain substantially from the Ensemble while others show minimal effects. We leave deeper investigations into model-specific benefits, such as predicting the suitability of DKPS-based methods for a particular model, to future work.

**Query set matters.** The bottom row of Figure 4 shows performance variation across different random query subsets. Each point represents the mean performance difference (Sample Score MAE minus Ensemble MAE) for a single randomly-sampled query set of size $m$, averaged across models. A point above 0 indicates that the Ensemble outperforms Sample Score for that query set. As can be seen in the figure, at small query budgets ($m \le 10$), the distributions span a wide range: some query sets yield substantial Ensemble improvements while others produce negligible or negative gains. This variance arises because the quality of the DKPS representations $\hat{\psi}$ depends on which queries are used to construct the distance matrix $D$ - with few queries, unlucky selections can produce uninformative representations. As query budget increases, the variance contracts, but poor query selection at low $m$ is precisely where DKPS-based methods would otherwise provide the largest savings. This motivates developing query selection strategies that move beyond uniform random sampling.

> **Figure 4.** Performance gain (MAE of Sample Score minus MAE of Ensemble regressor) on a per model basis (top) and a per query set basis (bottom) for the four representative subtasks. Each dot represents the average difference in performance across query sets (top) or across models (bottom). A A dot above 0 indicates that the Ensemble regressor is better than just using Sample Score. The majority of the mass of the distribution of the difference is above 0 for all number of queries and all tasks.

**Active query set selection protects against bad query sets.** We propose a simple offline selection strategy that leverages cached responses from reference models. Given a query budget $m$:

1. Sample $B$ candidate query sets of size $m$ uniformly at random.
2. For each candidate, construct DKPS representations of the reference models and fit a linear regressor to predict their known benchmark scores.
3. Compute the goodness-of-fit ($R^2$) between predicted and actual scores.
4. Select the query set that maximizes $R^2$.

If a query set produces DKPS representations that predict benchmark scores for reference models, it likely captures task-relevant model structure and will generalize to new models. This process operates entirely on cached responses and can be performed once and reused for all future evaluations at budget $m$.

Figure 5 demonstrates the effectiveness of this approach on the MATH counting and probability subtask with $m = 8$ queries. The top-left panel shows that $R^2$ on reference models correlates with prediction error on held-out models, validating $R^2$ as a selection criterion. The max-$R^2$ query set (red x) achieves lower error than the mean random query set. As can be seen in the top-center and bottom panels, this improvement is broad: the selected query set lies in the favorable tail of the error distribution and provides lower error across nearly all individual models. The top-right panel shows that the benefit of active selection diminishes as query budget increases - at larger $m$, random selection suffices. This is expected: active selection matters most where query set variance most limits DKPS effectiveness.

More broadly, DKPS-based prediction is complementary to query selection methods. Our $R^2$-based approach is one such method, but DKPS can equally operate on queries selected via other principled or brute force selection strategies - potentially compounding efficiency gains beyond what either approach achieves alone.

> **Figure 5.** Active query selection can improve query-efficiency of DKPS-based prediction methods. Top left. Relationship between MAE and linear goodness-of-fit ($R^2$) between DKPS representations of reference models and full benchmark score for $m = 8$ queries on the MATH counting and probability subtask. The highest $R^2$ (lowest $1 - R^2$) is highlighted with a red x. Top center. Histogram of MAE for different query subsets. Color indicates number of reference models. Using the query set that induces the DKPS representations that maximizes $R^2$ has a lower better than the average query set for both $n = 20$ and $n = ALL$. Top right. MAE versus $1 - R^2$ densities for different $(n,m)$ pairs. Bottom. MAE distribution across query sets for various models. If the red x is lower than the dotted line, the query set that maximized $R^2$ is preferred over the average query set.

## 5. Discussion

We proposed an approach to benchmark score prediction that leverages cached responses from previously-evaluated models via the Data Kernel Perspective Space. We established formal query-efficiency guarantees, proving that nearest neighbor regression in DKPS outperforms predicting benchmark scores using the model's score on a subset of queries under certain technical assumptions.

These theoretical predictions were validated empirically across diverse HELM-Lite tasks spanning mathematical reasoning, legal analysis, medical question answering, and machine translation. The Ensemble method - which adaptively combines DKPS-based prediction with direct sample scores - consistently achieved the best performance. We further demonstrated that offline query selection strategies can provide additional improvements to query efficiency. Overall, our results demonstrate that information encoded in cached responses enables more efficient performance prediction - an important capability as evaluation continues to scale in cost and complexity.

### Limitations and future work

**Extensions across modalities and metrics.** Our framework extends beyond some of the specific design choices made here. While we focused on language models with Frobenius norm on embedded responses, the approach applies to any modality (image, code, multimodal generation) where models can be embedded via appropriate functions $g : \mathcal{X} \to \mathbb{R}^p$, and to alternative distance metrics (Wasserstein, maximum mean discrepancy, task-specific similarities) that may better capture model relationships for particular benchmarks. Exploring these variations across evaluation scenarios represents a promising direction for future work.

**Stochastic scoring functions.** Our theoretical analysis assumes the mapping from a response to its score is deterministic. However, many modern evaluation frameworks use LLM-as-judge scoring (Zheng et al., 2023), where scores are stochastic and may depend on contextual factors beyond individual responses. Extending our framework to this setting is conceptually straightforward. DKPS representations can be constructed from multiple response samples, and scoring uncertainty can be propagated through the prediction pipeline. The established theoretical guarantees would similarly require modification. Our proof technique relies on smoothness in the (deterministic) mapping from $y$ to $\psi(Q)$. We conjecture that similar query-efficiency results hold under appropriate noise assumptions, though likely for $k$-nearest neighbors with $k \to \infty$ and $k/n \to 0$ as opposed to the current $k = 1$.

**Evaluation without response-level scores.** A subtle but important feature of DKPS-based methods is that they remain valid even when response-level scoring is unavailable or expensive. Traditional subset scoring methods require scoring each response to identify informative queries, but DKPS constructs representations purely from response embeddings without invoking the scoring function. This enables prediction in scenarios where: (1) scoring is proprietary or access-controlled (e.g., human evaluation), (2) scoring is computationally expensive (e.g., running code, simulation), or (3) scores are only available at the benchmark level, not per-query. Demonstration of the utility of DKPS to these settings is an exciting area of future work.

**Unstructured query sets and missing data.** Our analysis assumes all reference models are evaluated on the same query set, enabling direct construction of the distance matrix $D$. In practice, benchmark data often exhibits partial overlap - different models may be evaluated on different query subsets due to asynchronous evaluation, budget constraints, or benchmark evolution. Several approaches could extend DKPS to this setting. For example, restricting to models sharing a common query set (our current approach), using matrix completion methods (Candes & Recht, 2008) to estimate distances from incomplete data, or aligning separate DKPS representations via models evaluated on multiple query sets (Priebe et al., 2011). Understanding how query set overlap affects DKPS quality and developing principled aggregation methods would significantly broaden the practical reach of our framework, particularly for settings where models are continuously added with varying query coverage.

**Query efficiency in practice.** Our empirical results revealed efficiency heterogeneity across task. Understanding which task properties (e.g., response diversity, scoring function complexity, query difficulty distribution, alignment between embeddings and evaluation metrics) predict when DKPS-based methods excel would enable practitioners to assess applicability before deployment.

In terms of practical deployment, our results suggest a simple workflow: maintain cached responses from evaluated models, use the Ensemble method with offline query selection, and allocate approximately 10% of the full query budget for new model evaluation. Notably, our Leave-One-Family-Out evaluation protocol provides conservative estimates of real-world performance since in practice reference sets may include models from the same family as the target, yielding stronger cross-model signal and further improving query efficiency. As model zoos and benchmark suites continue to grow, integrating DKPS-based prediction into evaluation pipelines will yield substantial cumulative savings.

## Impact Statement & Acknowledgments

The methods proposed and study in this work reduce the computational cost of benchmark evaluation by up to 10x by leveraging cached responses from previously-evaluated models. Lower evaluation costs democratize access to comprehensive model assessment, enabling researchers and practitioners with limited budgets to make informed deployment decisions. We foresee no negative societal consequences of this work.

We gratefully acknowledge funding from Defense Advanced Research Projects Agency (DARPA) Artificial Intelligence Quantified (AIQ) award number HR00112520026.

## References

Aranyak Acharyya, Michael W. Trosset, Carey E. Priebe, and Hayden S. Helm. Consistent estimation of generative model representations in the data kernel perspective space, 2024. URL https://arxiv.org/abs/2409.17308.

Aranyak Acharyya, Joshua Agterberg, Youngser Park, and Carey E. Priebe. Concentration bounds on response-based vector embeddings of black-box generative models, 2025. URL https://arxiv.org/abs/2511.08307.

Andrew M. Bean et al. Scales++: Compute efficient evaluation subset selection with cognitive scales embeddings. arXiv preprint arXiv:2510.26384, 2025.

Ondrej Bojar, Christian Buck, Christian Federmann, Barry Haddow, Philipp Koehn, Johannes Leveling, Christof Monz, Pavel Pecina, Matt Post, Herve Saint-Amand, Radu Soricut, Lucia Specia, and Ales Tamchyna. Findings of the 2014 workshop on statistical machine translation. In Ondrej Bojar, Christian Buck, Christian Federmann, Barry Haddow, Philipp Koehn, Christof Monz, Matt Post, and Lucia Specia (eds.), Proceedings of the Ninth Workshop on Statistical Machine Translation, pp. 12-58, Baltimore, Maryland, USA, June 2014. Association for Computational Linguistics. doi: 10.3115/v1/W14-3302. URL https://aclanthology.org/W14-3302/.

Emmanuel J. Candes and Benjamin Recht. Exact matrix completion via convex optimization, 2008. URL https://arxiv.org/abs/0805.4471.

Mark Chen, Jerry Tworek, Heewoo Jun, Qiming Yuan, Henrique Ponde de Oliveira Pinto, Jared Kaplan, Harri Edwards, Yuri Burda, Nicholas Joseph, Greg Brockman, Alex Ray, Raul Puri, Gretchen Krueger, Michael Petrov, Heidy Khlaaf, Girish Sastry, Pamela Mishkin, Brooke Chan, Scott Gray, Nick Ryder, Mikhail Pavlov, Alethea Power, Lukasz Kaiser, Mohammad Bavarian, Clemens Winter, Philippe Tillet, Felipe Petroski Such, Dave Cummings, Matthias Plappert, Fotios Chantzis, Elizabeth Barnes, Ariel Herbert-Voss, William Hebgen Guss, Alex Nichol, Alex Paino, Nikolas Tezak, Jie Tang, Igor Babuschkin, Suchir Balaji, Shantanu Jain, William Saunders, Christopher Hesse, Andrew N. Carr, Jan Leike, Josh Achiam, Vedant Misra, Evan Morikawa, Alec Radford, Matthew Knight, Miles Brundage, Mira Murati, Katie Mayer, Peter Welinder, Bob McGrew, Dario Amodei, Sam McCandlish, Ilya Sutskever, and Wojciech Zaremba. Evaluating large language models trained on code, 2021. URL https://arxiv.org/abs/2107.03374.

Nan Chen, Hayden Helm, Youngser Park, Carey Priebe, and Soledad Villar. Extracting information from fine-tuned weights. In Non-Euclidean Foundation Models: Advancing AI Beyond Euclidean Frameworks, 2025. URL https://openreview.net/forum?id=zjwOD3Fwrq.

Francois Chollet. On the measure of intelligence, 2019. URL https://arxiv.org/abs/1911.01547.

Jaewon Chung, Benjamin D. Pedigo, Eric W. Bridgeford, Bijan K. Varjavand, Hayden S. Helm, and Joshua T. Vogelstein. Graspy: Graph statistics in python. Journal of Machine Learning Research, 20(158):1-7, 2019. URL http://jmlr.org/papers/v20/19-490.html.

Brandon Duderstadt, Hayden S. Helm, and Carey E. Priebe. Comparing foundation models using data kernels, 2023. URL https://arxiv.org/abs/2305.05126.

R. A. Fisher. The use of multiple measurements in taxonomic problems. Annals of Eugenics, 7(7):179-188, 1936.

Jianping Gou, Baosheng Yu, Stephen J. Maybank, and Dacheng Tao. Knowledge distillation: A survey. International Journal of Computer Vision, 129(6):1789-1819, March 2021. ISSN 1573-1405. doi: 10.1007/s11263-021-01453-z. URL http://dx.doi.org/10.1007/s11263-021-01453-z.

Neel Guha, Julian Nyarko, Daniel E. Ho, Christopher Re, Adam Chilton, Aditya Narayana, Alex Chohlas-Wood, Austin Peters, Brandon Waldon, Daniel N. Rockmore, Diego Zambrano, Dmitry Talisman, Enam Hoque, Faiz Surani, Frank Fagan, Galit Sarfaty, Gregory M. Dickinson, Haggai Porat, Jason Hegland, Jessica Wu, Joe Nudell, Joel Niklaus, John Nay, Jonathan H. Choi, Kevin Tobia, Margaret Hagan, Megan Ma, Michael Livermore, Nikon Rasumov-Rahe, Nils Holzenberger, Noam Kolt, Peter Henderson, Sean Rehaag, Sharad Goel, Shang Gao, Spencer Williams, Sunny Gandhi, Tom Zur, Varun Iyer, and Zehua Li. Legalbench: A collaboratively built benchmark for measuring legal reasoning in large language models, 2023. URL https://arxiv.org/abs/2308.11462.

Zeyu Han, Chao Gao, Jinyang Liu, Jeff Zhang, and Sai Qian Zhang. Parameter-efficient fine-tuning for large models: A comprehensive survey, 2024. URL https://arxiv.org/abs/2403.14608.

Hayden Helm, Ashwin de Silva, Joshua T. Vogelstein, Carey E. Priebe, and Weiwei Yang. Approximately optimal domain adaptation with fisher's linear discriminant. Mathematics, 12(5), 2024a. ISSN 2227-7390. doi: 10.3390/math12050746. URL https://www.mdpi.com/2227-7390/12/5/746.

Hayden Helm, Brandon Duderstadt, Youngser Park, and Carey Priebe. Tracking the perspectives of interacting language models. Proceedings of the 2024 Conference on Empirical Methods in Natural Language Processing, pp. 1508-1519, November 2024b. doi: 10.18653/v1/2024.emnlp-main.90. URL https://aclanthology.org/2024.emnlp-main.90/.

Hayden Helm, Aranyak Acharyya, Youngser Park, Brandon Duderstadt, and Carey Priebe. Statistical inference on black-box generative models in the data kernel perspective space. Findings of the Association for Computational Linguistics: ACL 2025, pp. 3955-3970, July 2025. doi: 10.18653/v1/2025.findings-acl.204. URL https://aclanthology.org/2025.findings-acl.204/.

Dan Hendrycks, Collin Burns, Saurav Kadavath, Akul Arora, Steven Basart, Eric Tang, Dawn Song, and Jacob Steinhardt. Measuring mathematical problem solving with the math dataset. NeurIPS, 2021.

Eliahu Horwitz, Nitzan Kurer, Jonathan Kahana, Liel Amar, and Yedid Hoshen. We should chart an atlas of all the world's models, 2025. URL https://arxiv.org/abs/2503.10633.

Kaiyi Huang, Chengqi Duan, Kaiyue Sun, Enze Xie, Zhenguo Li, and Xihui Liu. T2i-compbench++: An enhanced and comprehensive benchmark for compositional text-to-image generation, 2025. URL https://arxiv.org/abs/2307.06350.

Minyoung Huh, Brian Cheung, Tongzhou Wang, and Phillip Isola. The platonic representation hypothesis, 2024. URL https://arxiv.org/abs/2405.07987.

Di Jin, Eileen Pan, Nassim Oufattole, Wei-Hung Weng, Hanyi Fang, and Peter Szolovits. What disease does this patient have? a large-scale open domain question answering dataset from medical exams. arXiv preprint arXiv:2009.13081, 2020.

Alex Krizhevsky. Learning multiple layers of features from tiny images. Technical report, 2009.

Yann LeCun, Corinna Cortes, and CJ Burges. Mnist handwritten digit database. ATT Labs [Online]. Available: http://yann.lecun.com/exdb/mnist, 2, 2010.

Yang Li et al. Active evaluation acquisition for efficient llm benchmarking. 2024.

Percy Liang, Rishi Bommasani, Tony Lee, Dimitris Tsipras, Dilara Soylu, Michihiro Yasunaga, Yian Zhang, Deepak Narayanan, Yuhuai Wu, Ananya Kumar, et al. Holistic evaluation of language models. arXiv preprint arXiv:2211.09110, 2022.

Michael S Matena and Colin A Raffel. Merging models with fisher-weighted averaging. Advances in Neural Information Processing Systems, 35:17703-17716, 2022.

Niklas Muennighoff, Nouamane Tazi, Loic Magne, and Nils Reimers. Mteb: Massive text embedding benchmark, 2023. URL https://arxiv.org/abs/2210.07316.

Yotam Perlitz, Elron Bandel, Ariel Gera, Ofir Arviv, Liat Ein-Dor, Eyal Shnarch, Noam Slonim, Michal Shmueli-Scheuer, and Leshem Choshen. Efficient benchmarking (of language models). In Proceedings of the 2024 Conference of the North American Chapter of the Association for Computational Linguistics, pp. 2519-2536, 2024.

Felipe Maia Polo, Lucas Weber, Leshem Choshen, Yuekai Sun, Gongjun Xu, and Mikhail Yurochkin. tinybenchmarks: evaluating llms with fewer examples. In Proceedings of the 41st International Conference on Machine Learning, pp. 34303-34326, 2024.

Carey E. Priebe, David J. Marchette, Zhiliang Ma, and Sancar Adali. Manifold matching: Joint optimization of fidelity and commensurability, 2011. URL https://arxiv.org/abs/1112.5510.

Benjamin Recht, Rebecca Roelofs, Ludwig Schmidt, and Vaishaal Shankar. Do ImageNet classifiers generalize to ImageNet? In Kamalika Chaudhuri and Ruslan Salakhutdinov (eds.), Proceedings of the 36th International Conference on Machine Learning, volume 97 of Proceedings of Machine Learning Research, pp. 5389-5400. PMLR, 09-15 Jun 2019. URL https://proceedings.mlr.press/v97/recht19a.html.

Pranab Sahoo, Ayush Kumar Singh, Sriparna Saha, Vinija Jain, Samrat Mondal, and Aman Chadha. A systematic survey of prompt engineering in large language models: Techniques and applications, 2025. URL https://arxiv.org/abs/2402.07927.

Warren S Torgerson. Multidimensional scaling: I. theory and method. Psychometrika, 17(4):401-419, 1952.

Rajan Vivek, Kawin Ethayarajh, Diyi Yang, and Douwe Kiela. Anchor points: Benchmarking models with much fewer examples. In Yvette Graham and Matthew Purver (eds.), Proceedings of the 18th Conference of the European Chapter of the Association for Computational Linguistics (Volume 1: Long Papers), pp. 1576-1601, St. Julian's, Malta, March 2024. Association for Computational Linguistics. doi: 10.18653/v1/2024.eacl-long.95. URL https://aclanthology.org/2024.eacl-long.95/.

Shengyu Zhang, Linfeng Dong, Xiaoya Li, Sen Zhang, Xiaofei Sun, Shuhe Wang, Jiwei Li, Runyi Hu, Tianwei Zhang, Fei Wu, and Guoyin Wang. Instruction tuning for large language models: A survey, 2025. URL https://arxiv.org/abs/2308.10792.

Lianmin Zheng, Wei-Lin Chiang, Ying Sheng, Siyuan Zhuang, Zhanghao Wu, Yonghao Zhuang, Zi Lin, Zhuohan Li, Dacheng Li, Eric P. Xing, Hao Zhang, Joseph E. Gonzalez, and Ion Stoica. Judging llm-as-a-judge with mt-bench and chatbot arena, 2023. URL https://arxiv.org/abs/2306.05685.

Mu Zhu and Ali Ghodsi. Automatic dimensionality selection from the scree plot via the use of profile likelihood. Computational Statistics & Data Analysis, 51(2):918-930, 2006.

## A. Experiment details

**Table 2.** List of model families.

| Family | Count | Models |
|---|---:|---|
| 01-ai | 3 | yi-34b, yi-6b, yi-large-preview |
| AlephAlpha | 3 | luminous-base, luminous-extended, luminous-supreme |
| ai21 | 5 | j2-grande, j2-jumbo, jamba-1.5-large, jamba-1.5-mini, jamba-instruct |
| allenai | 1 | olmo-7b |
| amazon | 3 | nova-lite-v1, nova-micro-v1, nova-pro-v1 |
| anthropic | 11 | claude-2.0, claude-2.1, claude-3-5-haiku-20241022, claude-3-5-sonnet-20240620, claude-3-5-sonnet-20241022, claude-3-haiku-20240307, claude-3-opus-20240229, claude-3-sonnet-20240229, claude-instant-1.2, claude-instant-v1, claude-v1.3 |
| cohere | 4 | command, command-light, command-r, command-r-plus |
| databricks | 1 | dbrx-instruct |
| deepseek-ai | 2 | deepseek-llm-67b-chat, deepseek-v3 |
| google | 13 | gemini-1.0-pro-001, gemini-1.0-pro-002, gemini-1.5-flash-001, gemini-1.5-flash-002, gemini-1.5-pro-001, gemini-1.5-pro-002, gemini-1.5-pro-preview-0409, gemini-2.0-flash-exp, gemma-2-27b-it, gemma-2-9b-it, gemma-7b, text-bison@001, text-unicorn@001 |
| meta | 12 | llama-2-13b, llama-2-70b, llama-2-7b, llama-3-70b, llama-3-8b, llama-3.1-405b-instruct-turbo, llama-3.1-70b-instruct-turbo, llama-3.1-8b-instruct-turbo, llama-3.2-11b-vision-instruct-turbo, llama-3.2-90b-vision-instruct-turbo, llama-3.3-70b-instruct-turbo, llama-65b |
| microsoft | 3 | phi-2, phi-3-medium-4k-instruct, phi-3-small-8k-instruct |
| mistralai | 9 | mistral-7b-instruct-v0.3, mistral-7b-v0.1, mistral-large-2402, mistral-large-2407, mistral-medium-2312, mistral-small-2402, mixtral-8x22b, mixtral-8x7b-32kseqlen, open-mistral-nemo-2407 |
| nvidia | 1 | nemotron-4-340b-instruct |
| openai | 9 | gpt-3.5-turbo-0613, gpt-4-0613, gpt-4-1106-preview, gpt-4-turbo-2024-04-09, gpt-4o-2024-05-13, gpt-4o-2024-08-06, gpt-4o-mini-2024-07-18, text-davinci-002, text-davinci-003 |
| qwen | 8 | qwen1.5-110b-chat, qwen1.5-14b, qwen1.5-32b, qwen1.5-72b, qwen1.5-7b, qwen2-72b-instruct, qwen2.5-72b-instruct-turbo, qwen2.5-7b-instruct-turbo |
| snowflake | 1 | snowflake-arctic-instruct |
| tiiuae | 2 | falcon-40b, falcon-7b |
| upstage | 1 | solar-pro-241126 |
| writer | 3 | palmyra-x-004, palmyra-x-v2, palmyra-x-v3 |

**Table 3.** Missing models per task.

| Dataset / Subtask | Present | Missing | Missing Models (by family) |
|---|---:|---:|---|
| legalbench-subset=abercrombie | 93 | 2 | mistralai: mistral-large-2402, mistral-small-2402 |
| legalbench-subset=corporate lobbying | 93 | 2 | mistralai: mistral-large-2402, mistral-small-2402 |
| legalbench-subset=function of decision section | 93 | 2 | mistralai: mistral-large-2402, mistral-small-2402 |
| legalbench-subset=international citizenship questions | 93 | 2 | mistralai: mistral-large-2402, mistral-small-2402 |
| legalbench-subset=proa | 93 | 2 | mistralai: mistral-large-2402, mistral-small-2402 |
| math-subject=algebra | 95 | 0 | - |
| math-subject=counting and probability | 95 | 0 | - |
| math-subject=geometry | 95 | 0 | - |
| math-subject=intermediate algebra | 95 | 0 | - |
| math-subject=number theory | 95 | 0 | - |
| math-subject=prealgebra | 95 | 0 | - |
| math-subject=precalculus | 95 | 0 | - |
| med qa | 95 | 0 | - |
| wmt 14-language pair=cs-en | 95 | 0 | - |
| wmt 14-language pair=de-en | 95 | 0 | - |
| wmt 14-language pair=fr-en | 94 | 1 | ai21: jamba-instruct |
| wmt 14-language pair=hi-en | 95 | 0 | - |
| wmt 14-language pair=ru-en | 95 | 0 | - |
