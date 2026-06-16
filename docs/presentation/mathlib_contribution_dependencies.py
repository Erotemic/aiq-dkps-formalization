import networkx as nx


def build_mathlib_candidate_graph() -> nx.DiGraph:
    """
    Build a dependency graph of high-level Mathlib contribution candidates.

    Edge convention:
        A -> B means "A depends on B".
    """
    G = nx.DiGraph()

    nodes = {
        "Small probability/QoL lemmas": {"rank": 11, "value": "low-medium"},
        "Convergence-in-measure constructors": {"rank": 10, "value": "medium"},
        "Elementary eigenvalue concentration engine": {"rank": 7, "value": "medium-high"},
        "Entrywise-to-operator norm perturbation": {"rank": 6, "value": "high"},
        "Entrywise-to-eigenvalue perturbation": {"rank": 6, "value": "high"},
        "Davis-Kahan / Weyl / Courant-Fischer spectral perturbation stack": {
            "rank": 1,
            "value": "very high",
        },
        "Courant-Fischer theorem and helper lemmas": {"rank": 1, "value": "very high"},
        "Weyl eigenvalue perturbation": {"rank": 1, "value": "very high"},
        "Davis-Kahan / sin-theta perturbation": {"rank": 1, "value": "very high"},
        "Gram-matrix rigidity": {"rank": 2, "value": "very high"},
        "Rank-controlled PSD Gram realization": {"rank": 3, "value": "very high"},
        "Quantitative polar factor / near-isometry theorem": {"rank": 5, "value": "high"},
        "Spectral-transform / CFC measurability": {"rank": 4, "value": "high"},
        "Compact-existential measurability": {"rank": 8, "value": "medium-high"},
        "Approximate-minimizer stability": {"rank": 9, "value": "medium"},
    }

    G.add_nodes_from(nodes.items())

    edges = [
        ("Convergence-in-measure constructors", "Small probability/QoL lemmas"),
        ("Elementary eigenvalue concentration engine", "Small probability/QoL lemmas"),
        ("Elementary eigenvalue concentration engine", "Entrywise-to-eigenvalue perturbation"),

        ("Entrywise-to-eigenvalue perturbation", "Entrywise-to-operator norm perturbation"),
        (
            "Entrywise-to-eigenvalue perturbation",
            "Davis-Kahan / Weyl / Courant-Fischer spectral perturbation stack",
        ),
        (
            "Davis-Kahan / Weyl / Courant-Fischer spectral perturbation stack",
            "Courant-Fischer theorem and helper lemmas",
        ),
        (
            "Davis-Kahan / Weyl / Courant-Fischer spectral perturbation stack",
            "Weyl eigenvalue perturbation",
        ),
        (
            "Davis-Kahan / Weyl / Courant-Fischer spectral perturbation stack",
            "Davis-Kahan / sin-theta perturbation",
        ),
        ("Weyl eigenvalue perturbation", "Courant-Fischer theorem and helper lemmas"),
        ("Davis-Kahan / sin-theta perturbation", "Weyl eigenvalue perturbation"),
        ("Davis-Kahan / sin-theta perturbation", "Courant-Fischer theorem and helper lemmas"),

        ("Gram-matrix rigidity", "Rank-controlled PSD Gram realization"),
        ("Quantitative polar factor / near-isometry theorem", "Gram-matrix rigidity"),

        ("Approximate-minimizer stability", "Compact-existential measurability"),
        ("Spectral-transform / CFC measurability", "Compact-existential measurability"),
        (
            "Spectral-transform / CFC measurability",
            "Davis-Kahan / Weyl / Courant-Fischer spectral perturbation stack",
        ),
    ]

    G.add_edges_from(edges)

    if not nx.is_directed_acyclic_graph(G):
        raise RuntimeError(f"Dependency graph has a cycle: {nx.find_cycle(G)}")

    return G


if __name__ == "__main__":
    G = build_mathlib_candidate_graph()

    print("Dependency tree")
    print("A -> B means: A depends on B")
    print()

    # Shows successors, i.e. dependencies under our edge convention.
    nx.write_network_text(G)

    print()
    print("Dependency-first order")
    print("----------------------")

    # Because edges point from dependent to dependency, reverse before topo-sort.
    for i, node in enumerate(nx.topological_sort(G.reverse(copy=False)), start=1):
        print(f"{i:2d}. {node}")
