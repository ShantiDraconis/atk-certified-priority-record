# ATK — Revisão de linguagem matemática e dependências

**Estado:** REVIEW; não é certificado terminal. Este documento registra caminhos de branches históricas; não modifica os arquivos originais nessas branches.

## 1. P01 model witness

- Branch de origem: `main`
- Arquivo: `snapshots/m-core-p-vs-np/probe/P01MachineConstructionExpectedFailure.lean`
- Classificação: `CONDITIONAL` / `MODEL_PROVEN` / `OPEN_OBLIGATION` conforme a prova e dependências verificadas.
- Formulação correta: Prova de construção P01 no modelo especificado; não implica SAT ∉ P nem P ≠ NP.
- Ação: conferir definição do alvo, hipóteses, imports e `#print axioms` antes de qualquer promoção.

Não substituir `axiom`, `sorry` ou hipóteses por texto; obter provas matemáticas independentes quando necessárias.
