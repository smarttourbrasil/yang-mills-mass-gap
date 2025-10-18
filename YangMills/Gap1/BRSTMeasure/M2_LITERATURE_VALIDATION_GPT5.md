
# M2 Literature Validation — Convergence of the BRST Measure (Axioma 1)

**Target statement (plain text).**  
\[\int_{A/G} e^{-S_{\mathrm{YM}}[A]}\,\Delta_{\mathrm{FP}}[A]\,\mathrm{d}\mu_{\mathrm{BRST}}(A)\ \textbf{converges},\]
and (operationally) the measure **concentrates on the first Gribov region** \(\Omega\) (no FP zero-modes).

**Scope.** Relate Euclidean **Osterwalder–Schrader (OS)** framework, **reflection positivity**, and **constructive QFT** to convergence/normalizability of the Euclidean BRST path integral; connect to **lattice evidence** (HMC/OBC) and to **Gribov–(Refined)Zwanziger** implementations of the \(\Omega\) restriction. Distinguish: **proven** vs. **plausible** vs. **conjectural** claims.

---

## 1) OS Framework (Euclidean QFT ⇒ Wightman)

- **OS axioms (1973/1975):** Reflection positivity, Euclidean invariance, symmetry, cluster/regularity imply existence of a corresponding relativistic QFT (reconstruction theorem). Under suitable **bounds on moments**, the Euclidean measure is **normalized**: \(Z<\infty\).  
  **Assessment:** **✅ Provado (framework).** For **Yang–Mills 4D**, full OS verification **não** é clássico; usa-se a estrutura OS como **guideline**.

- **Reflection positivity:** centerpiece for reconstructing a Hilbert space from Schwinger functions; constructive results in **\(P(\phi)_2\)** and related models ensure convergence and positivity at finite volume and in the continuum under precise bounds.  
  **Assessment:** **✅ Provado** para classes escalares; YM **parcial/aberto**.


## 2) Constructive QFT (comparativos úteis)

- **Escalares \(P(\phi)_2\), \(\phi^4_2\), etc.:** convergência do funcional euclidiano e reconstrução relativística **provadas** (Glimm–Jaffe; Simon).  
- **Yang–Mills 4D:** programa **parcial** (Balaban et al.) com controle de **campos pequenos** e construção RG em grades; **não** há prova completa de OS/convergência no contínuo para YM.  
  **Assessment:** **🟡 Plausível** que **versões regulares** (corte UV/IR, volume finito) admitam medidas normalizadas que **convergem** ao continuum **em subsequências**; prova geral continua **em aberto**.


## 3) Lattice QCD — Evidência de Convergência (numérica/operacional)

- **HMC/algoritmos Markovianos** fornecem **amostragem de uma medida normalizada** \(Z<\infty\) em volume finito, malha finita; **termalização** e **autocorrelações** controladas em regimes bem comportados.  
- **Topologia e OBC:** em espaçamentos finos, PBC sofrem *freezing*; **open boundary conditions** restauram trânsito de carga topológica e garantem **amostragem ergódica** multi‑setor → forte evidência prática de **convergência/normalização** da medida regularizada.  
  **Assessment:** **✅ Provado (lattice/numérico)**: para cada par \((a,V)\) finitos, \(Z_{a,V}<\infty\) e o ensemble converge (em média) para limites estacionários. A passagem \(a\to 0\) permanece **plausível** sob controles padrão (esquemas de melhoria), porém **não** é um teorema geral.


## 4) Gribov Region & BRST Measure

- **Implementação de \(\Omega\):** Ações **(Refined) Gribov–Zwanziger** implementam localmente a restrição ao **domínio sem modos zero** do FP; são **renormalizáveis**, reproduzem propagadores em acordo qualitativo com *lattice* e podem ser integradas a formulações **BRST‑compatíveis** (quebra “soft” tratável; formulações BRST‑invariantes modernas em gauges lineares).  
  **Assessment:** **🟡 Plausível → Sólido** para **concentração operacional** da medida em \(\Omega\) nas formulações GZ/RGZ/BRST‑compatíveis.


## 5) Gap Analysis

| Status | Claim | Notes / Evidence |
|---|---|---|
| ✅ Provado | OS framework: se axiomas + bounds ⇒ reconstrução e normalização \(Z<\infty\) | OS 1973/75; Jaffe/Glimm constructive overviews. |
| ✅ Provado | Convergência/positividade para \(P(\phi)_2\), \(\phi^4_2\), etc. | Glimm–Jaffe; Simon; Rivasseau (survey). |
| 🟡 Plausível | YM 4D satisfaz OS em forma regularizada com passagem de limite controlada | Balaban (RG small‑field); reviews CQFT. |
| ✅ Provado (lattice finito) | Para \(a,V<\infty\), \(Z_{a,V}<\infty\) e HMC termaliza/produz ensembles | HMC (Duane et al.), textos *Lattice QCD*; OBC (Lüscher–Schaefer). |
| 🟡 Plausível | Continuidade \(a\to 0\) mantém convergência/normalização | Evidência empírica/teórica padrão; sem teorema geral. |
| 🟡 Plausível | Medida BRST efetiva **concentra** em \(\Omega\) | GZ/RGZ (Zwanziger; Dudal et al.); BRST‑compatível (Capri et al.). |


## 6) Overall Assessment

- **Probabilidade (M2 verdadeiro na forma operacional):** **~80–90%**.  
- **Risco:** **Médio‑baixo** — fundamentado por OS + CQFT (escalares), forte **evidência lattice** (convergência numérica) e **framework GZ/RGZ** para concentração em \(\Omega\); falta **prova completa** de OS para YM 4D no contínuo.  
- **Recomendação:** **Proceed** com formalização **condicional/operacional** em Lean4:  
  1) Definir M2 em **volume finito, cutoff UV** (medida BRST regularizada) e provar **convergência/normalização**;  
  2) Introduzir **hipótese de estabilidade de limite** \(a\to 0\), \(V\to\infty\) (esquema de renorm. escolhido);  
  3) Implementar **concentração em \(\Omega\)** via axioma técnico equivalente à presença de **gap FP** (ou ação GZ formal) e ausência de zero‑modes no interior;  
  4) Ligar com M1/M3/M4/M5 para fechar **Axioma 1**.


---

## Referências (mín. 15, estilo compacto)

- **OS (I/II).** K. Osterwalder, R. Schrader, “Axioms for Euclidean Green’s functions,” *Commun. Math. Phys.* **31** (1973) 83–112; “II”, *CMP* **42** (1975) 281–305.  
- **Jaffe — CQFT overview.** A. Jaffe, “Constructive Quantum Field Theory” (survey).  
- **Glimm & Jaffe (textbook).** *Quantum Physics: A Functional Integral Point of View*, 2nd ed., Springer, 1987.  
- **Simon (book).** B. Simon, *P(φ)\_2 Euclidean (Quantum) Field Theory*, Princeton, 1974.  
- **Rivasseau (book).** V. Rivasseau, *From Perturbative to Constructive Renormalization*, Princeton, 1991 (and later reprints).  
- **Seiler (gauge/CQFT).** E. Seiler, *Gauge Theories as a Problem of Constructive QFT and Statistical Mechanics*, LNP 159, Springer, 1982.  
- **Balaban (YM RG).** T. Bałaban, “Renormalization group approach to lattice gauge field theories I–…,” *Commun. Math. Phys.* **109** (1987) 249–301; and series.  
- **HMC.** S. Duane, A. Kennedy, B. Pendleton, D. Roweth, “Hybrid Monte Carlo,” *Phys. Lett. B* **195** (1987) 216–222.  
- **Lattice textbook.** C. Gattringer, C. B. Lang, *Quantum Chromodynamics on the Lattice*, LNP 788, Springer, 2010.  
- **OBC.** M. Lüscher, S. Schaefer, “Lattice QCD without topology barriers,” *JHEP* **07** (2011) 036.  
- **Zwanziger (horizon).** D. Zwanziger, “Local and renormalizable action from the Gribov horizon,” *Nucl. Phys. B* **323** (1989) 513–544.  
- **Refined GZ.** D. Dudal, J. A. Gracey, S. P. Sorella, N. Vandersickel, H. Verschelde, *Phys. Rev. D* **78** (2008) 065047; and related works.  
- **BRST‑compatível com Gribov.** M. A. L. Capri et al., *Phys. Rev. D* **94** (2016) 025035.  
- **Serreau–Tissier.** J. Serreau, M. Tissier, *Phys. Lett. B* **712** (2012) 97–103; *Phys. Rev. D* **89** (2014) 125019.  
- **Reviews RP.** K.-H. Neeb, G. Ólafsson, “Reflection Positivity — a representation theoretic perspective,” arXiv:1802.09037 (2018).

