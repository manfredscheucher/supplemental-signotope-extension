# Supplemental Material — An Extension Theorem for Signotopes

This repository contains supplemental source code and data for the article:

> **An Extension Theorem for Signotopes**  
> Helena Bergold, Stefan Felsner, and Manfred Scheucher  
> *39th International Symposium on Computational Geometry (SoCG 2023)*  
> LIPIcs, Volume 258, pp. 17:1–17:14  
> DOI: [10.4230/LIPIcs.SoCG.2023.17](https://doi.org/10.4230/LIPIcs.SoCG.2023.17)  
> arXiv: [2303.04079](https://arxiv.org/abs/2303.04079)

---

## Abstract

In 1926, Levi showed that for every pseudoline arrangement 𝒜 and two points in the plane, 𝒜 can be extended by a pseudoline containing the two prescribed points. Extendability was later studied for arrangements of pseudohyperplanes in higher dimensions. While extending a proper hyperplane arrangement in ℝ^d with a hyperplane through d prescribed points is trivial, Richter-Gebert found an arrangement of pseudoplanes in ℝ³ that cannot be extended with a pseudoplane through two particular prescribed points.

This article investigates the extendability of **signotopes** — a combinatorial structure encoding a rich subclass of pseudohyperplane arrangements. The main result is that **signotopes of odd rank are extendable**: for any two prescribed crossing points, a new element containing them can always be added. Furthermore, the authors conjecture that non-extendable signotopes exist in all even ranks r ≥ 4. This conjecture is supported by explicit counterexamples in ranks 4, 6, 8, 10, and 12, discovered using a **SAT-based search**.

---

## Repository Structure

```
.
├── final/          # Code and data for the final journal version
├── socg2023/       # Code and data for the SoCG 2023 conference version
└── LICENSE         # MIT License
```

### `socg2023/`
Contains the supplemental code and data accompanying the SoCG 2023 conference paper.

### `final/`
Contains the supplemental code and data for the final (journal) version of the paper, which extends and refines the conference results.

---

## Methods

The computational experiments use **Boolean satisfiability (SAT) solving** to search for non-extendable signotopes in even ranks. The code relies on standard Python SAT interfaces, in particular:

- [PySAT](https://pysathq.github.io/) — Python toolkit for prototyping with SAT oracles
- [pycosat](https://pypi.org/project/pycosat/) — Python bindings to PicoSAT
- [CaDiCaL](https://github.com/arminbiere/cadical) — high-performance SAT solver

---

## Keywords

arrangement of pseudolines · extendability · Levi's extension lemma · arrangement of pseudohyperplanes · signotope · oriented matroid · partial order · Boolean satisfiability (SAT)

---

## Citation

If you use this code or data in your research, please cite:

```bibtex
@InProceedings{bergold_et_al:LIPIcs.SoCG.2023.17,
  author    = {Bergold, Helena and Felsner, Stefan and Scheucher, Manfred},
  title     = {{An Extension Theorem for Signotopes}},
  booktitle = {39th International Symposium on Computational Geometry (SoCG 2023)},
  pages     = {17:1--17:14},
  series    = {Leibniz International Proceedings in Informatics (LIPIcs)},
  volume    = {258},
  year      = {2023},
  publisher = {Schloss Dagstuhl -- Leibniz-Zentrum f{\"u}r Informatik},
  doi       = {10.4230/LIPIcs.SoCG.2023.17},
  url       = {https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.SoCG.2023.17}
}
```

---

## Funding

- Helena Bergold: DFG Research Training Group *Facets of Complexity* (DFG-GRK 2434)
- Stefan Felsner: DFG Grant FE 340/13-1
- Manfred Scheucher: DFG Grant SCHE 2214/1-1

---

## License

This project is licensed under the [MIT License](LICENSE).  
Copyright © 2023 Helena Bergold, Stefan Felsner, and Manfred Scheucher.
