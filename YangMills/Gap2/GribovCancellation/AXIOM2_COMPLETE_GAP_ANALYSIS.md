
# L1–L4–L5 — Comparative Assessment (Axioma 2)

| Lemma | Plausibilidade | Risco | Literatura | Recomendação |
|---|---:|---:|---|---|
| **L1 (FP Parity)** | **70–80%** (condicional à região \(\Omega\)/FMR) | Médio | Forte para Index/Anomalias; fraca para paridade FP≡\((-1)^{\mathrm{ind}}\) global | **Proceed (cond.)** |
| **L4 (BRST‑Exactness)** | **65–75%** (exatidão sob \(P\) realizável via BRST/CP) | Médio | Muito forte para BRST/cohomologia; ponte com \(P\) setorial é nova | **Refine** (definir \(P\) operacional + caso‑teste) |
| **L5 (Regularity \(\Omega\))** | **75–85%** (convexidade/estrutura bem estabelecidas) | Baixo–Médio | Dell’Antonio–Zwanziger; (R)GZ; evidência numérica | **Proceed** |

**Ordem sugerida de formalização (facilidade → difícil):**  
1) **L5** → 2) **L1 (condicional)** → 3) **L4**.

**Notas para implementação (Lean4):**  
- **L5:** axiomatizar convexidade de \(\Omega\) e ausência de autovalores nulos no interior; usar estratificação para manejar a fronteira.  
- **L1:** trabalhar **dentro** de \(\Omega\)/FMR para fixar o sinal de \(\det M_{\text{FP}}\); ligar paridade a um índice discreto definido por homotopia (não necessariamente o índice de Dirac global).  
- **L4:** escolher **observáveis** e um \(P\) **operacional** (CP ∘ matching de lumps via flow) e provar exatidão usando **descent**/cochain homotopy.
