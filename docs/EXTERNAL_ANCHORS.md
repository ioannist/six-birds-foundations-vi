# External anchors — every non-corpus citation in `paper/references.bib`

Compiled 2026-09-02 (pre-ship audit, Phase 3). Corpus self-citations are listed in
`PRESHIP_AUDIT.md` §0 with the Zenodo DOIs printed in the vendored files. No entry was removed from
the text as unverifiable: every external citation either has verified metadata (V-web, V-ledger,
V-ext) or is a standard reference whose transcribed metadata is consistent with library records
(T); the two informally sourced items (Brown MathPages; the Fourmilab note) are labelled as such in
the text and here. Five entries were corrected in authorship (Boyar et al. author list; Greenberg–Hastings missing
coauthor; Breuer–Lötter–van der Merwe completed; Agrawal and Breuer given names), three in page
numbers (de Grey; Falconer; Shechtman et al. end page), and one uncited corpus entry removed
(`Tsiokos2026Adequacy`). The mechanical field-by-field record of every bibliography change is in
the last section of this file. Three verified primary sources were added
(Goodstein 1944; Sylvester 1880; Jeandel–Rao 2021), and one verified but uncited entry
(`Plouffe2025`) is now cited.

Columns: key | verified metadata (as it will be printed) | verification (V-web = checked against publisher/index page on 2026-09-02; V-ledger = verified in `design/10_FACT_CHECK_LEDGER.md` on 2026-07-08; V-ext = confirmed in the external review cycle; T = transcribed from the dossier, well-known standard reference, metadata consistent with library records but not re-fetched today) | result(s) it supports | correction made in this audit.

| Key | Verified metadata | Verification | Supports | Correction |
|---|---|---|---|---|
| Lagarias1985 | J. C. Lagarias, "The 3x+1 problem and its generalizations," Amer. Math. Monthly 92(1) (1985) 3–23, DOI 10.2307/2322189 (resolves to JSTOR 2322189) | V-web | G1 Collatz background only (survey); the ledger, ghost, shadowing and cycle facts are ELEMENTARY, re-derived on the page | DOI added |
| Lagarias2010 | J. C. Lagarias (ed.), *The Ultimate Challenge: The 3x+1 Problem*, AMS, 2010 | T | G1 background | — |
| Tao2019Collatz | T. Tao, "Almost all orbits of the Collatz map attain almost bounded values," Forum Math. Pi 10 (2022) e12, DOI 10.1017/fmp.2022.8; arXiv:1909.03562 | V-web, V-ext | G1 nonclaim (probabilistic status) | published version added |
| GuySelfridge1975 | R. K. Guy, J. L. Selfridge, "What drives an aliquot sequence?," Math. Comp. 29 (1975) 101–107 | V-web | G1 aliquot instantiation | — |
| GuyUnsolved | R. K. Guy, *Unsolved Problems in Number Theory*, 3rd ed., Springer, 2004 | T | G1 aliquot (Catalan–Dickson open) | year added |
| Liberzon2003 | D. Liberzon, *Switching in Systems and Control*, Birkhäuser, 2003 | T | G1 structural instantiation | — |
| AgrawalChatterjeeNovotny2017 | Sheshansh Agrawal, K. Chatterjee, P. Novotný, "Lexicographic ranking supermartingales…," Proc. ACM Program. Lang. 2 (POPL) (2018) 34:1–34:32, DOI 10.1145/3158122; arXiv:1709.04037 | V-web | G1 structural instantiation | **first author's given name corrected** (bib had "Sourabh"); published version added |
| LeeJonesBenAmram2001 | C. S. Lee, N. D. Jones, A. M. Ben-Amram, "The size-change principle for program termination," POPL 2001, ACM SIGPLAN Notices 36(3) (2001) 81–92 | V-web | G1 calibration | — |
| Goodstein1944 (new) | R. L. Goodstein, "On the restricted ordinal theorem," J. Symbolic Logic 9 (1944) 33–41 | V-web | G2 calibration (primary source of Goodstein's theorem) | added |
| KirbyParis1982 | L. Kirby, J. Paris, "Accessible independence results for Peano arithmetic," Bull. London Math. Soc. 14(4) (1982) 285–293 | V-ext | G2(b) price | — |
| Floyd1967 | R. W. Floyd, "Assigning meanings to programs," Proc. Sympos. Appl. Math. 19 (1967) 19–32 | V-web | G2(a) (RECOVERED STANDARD: well-founded ranking) | — |
| Dershowitz1982 | N. Dershowitz, "Orderings for term-rewriting systems," Theoret. Comput. Sci. 17(3) (1982) 279–301 | V-web | G2 instantiation | — |
| Gentzen1936 | G. Gentzen, "Die Widerspruchsfreiheit der reinen Zahlentheorie," Math. Ann. 112 (1936) 493–565 | V-web | G2 instantiation | — |
| DershowitzManna1979 | N. Dershowitz, Z. Manna, "Proving termination with multiset orderings," Comm. ACM 22(8) (1979) 465–476 | V-web | G2 AOR-tie instantiation | — |
| Tarjan1985 | R. E. Tarjan, "Amortized computational complexity," SIAM J. Alg. Disc. Meth. 6(2) (1985) 306–318 | V-web | G3 (RECOVERED STANDARD: potential method) | — |
| CormenEtAl | T. H. Cormen, C. E. Leiserson, R. L. Rivest, C. Stein, *Introduction to Algorithms*, 3rd ed., MIT Press, 2009 | T | G3 calibrations | year added |
| SleatorTarjan1985 | D. D. Sleator, R. E. Tarjan, "Self-adjusting binary search trees," J. ACM 32(3) (1985) 652–686 | V-ext | G3 splay instantiation | — |
| Willems1972 | J. C. Willems, "Dissipative dynamical systems, Part I," Arch. Rational Mech. Anal. 45 (1972) 321–351 | V-web | G3 structural | — |
| OzelEtAl | O. Ozel et al., "Transmission with energy harvesting nodes in fading wireless channels: optimal policies," IEEE J. Sel. Areas Commun. 29(8) (2011) 1732–1743; arXiv:1106.1595 | V-web | G3 structural | published version added |
| YangUlukus | J. Yang, S. Ulukus, "Optimal packet scheduling in an energy harvesting communication system," IEEE Trans. Commun. 60(1) (2012) 220–230; arXiv:1010.1295 | V-web | G3 structural | published version added |
| Fibonacci | L. Pisano (Fibonacci), *Liber Abaci* (1202); English translation L. E. Sigler, Springer, 2002 | T | G4 calibration | entry made `@misc` with year and translation |
| Sylvester1880 (new) | J. J. Sylvester, "On a point in the theory of vulgar fractions," Amer. J. Math. 3(4) (1880) 332–335 | V-web | G4 calibration (greedy algorithm) | added |
| Eppstein1995 | D. Eppstein, "Ten algorithms for Egyptian fractions," Mathematica in Education and Research 4(2) (1995) 5–15 | V-web | G4 calibration | pages added |
| Mordell1969 | L. J. Mordell, *Diophantine Equations*, Academic Press, 1969 | V-ledger | G4 Erdős–Straus identities (secondary-sourced, flagged in text) | — |
| ElsholtzTao2013 | C. Elsholtz, T. Tao, "Counting the number of solutions to the Erdős–Straus equation on unit fractions," J. Aust. Math. Soc. 94(1) (2013) 50–105 | V-ledger | G4 density evidence | — |
| Vaughan1970 | R. C. Vaughan, "On a problem of Erdős, Straus and Schinzel," Mathematika 17(2) (1970) 193–198 | V-ledger | G4 density evidence | — |
| Hough2015 | R. Hough, "Solution of the minimum modulus problem for covering systems," Ann. of Math. 181(1) (2015) 361–382 | V-ext | G4 covering-system instantiation | — |
| Risch1969 | R. H. Risch, "The problem of integration in finite terms," Trans. AMS 139 (1969) 167–189 | V-web | G4 structural | — |
| Bronstein2005 | M. Bronstein, *Symbolic Integration I*, 2nd ed., Springer, 2005 | T | G4 structural | — |
| ClarkeEtAl2003 | E. Clarke, O. Grumberg, S. Jha, Y. Lu, H. Veith, "Counterexample-guided abstraction refinement for symbolic model checking," J. ACM 50(5) (2003) 752–794 | V-web | G4 structural | — |
| OEIS-A060382 | OEIS A060382 (accessed 2026-09-02; "Only a(2) is proved") | V-web | G5 base-2 calibration status | access date added |
| Brown-MathPages | K. Brown, "Digit reversal sums leading to palindromes," MathPages kmath004 (informally sourced; no peer-reviewed version located) | V-web, V-ledger | G5 base-2 calibration (informal) | — |
| Walker-Fourmilab | J. Walker, "Three Years Of Computing: Final Report On The Palindrome Quest," Fourmilab, 1990 (web page; informal source) | V-web | G5 Lychrel status | title as printed by the source; year and URL added |
| Kocher1996 | P. C. Kocher, "Timing attacks on implementations of Diffie-Hellman, RSA, DSS, and other systems," Advances in Cryptology — CRYPTO '96, LNCS 1109, Springer, 104–113 | V-web | G5 structural | booktitle, series, volume, publisher and pages added |
| Higham2002 | N. J. Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed., SIAM, 2002 | T | G5 structural | — |
| AlloucheShallit2003 | J.-P. Allouche, J. Shallit, *Automatic Sequences*, Cambridge UP, 2003 | T | G5 instantiation | — |
| OEIS-A005132, OEIS-A057167 | OEIS entries (accessed 2026-09-02) | V-ext | G6 Recamán status | access date added |
| MadrasSlade1993 | N. Madras, G. Slade, *The Self-Avoiding Walk*, Birkhäuser, 1993 | T | G6 structural | — |
| Flory1953 | P. J. Flory, *Principles of Polymer Chemistry*, Cornell UP, 1953 | T | G6 structural | — |
| BellemareEtAl2016 | M. G. Bellemare et al., "Unifying count-based exploration and intrinsic motivation," NeurIPS 29 (2016) | T | G6 structural | — |
| BorodinElYaniv1998 | A. Borodin, R. El-Yaniv, *Online Computation and Competitive Analysis*, Cambridge UP, 1998 | T | G6 structural | — |
| BoyarEtAl | J. Boyar, L. M. Favrholdt, M. Kotrbčík, K. S. Larsen, "Relaxing the irrevocability requirement for online graph algorithms," Algorithmica 84 (2022) 1916–1951 (WADS 2017); arXiv:1704.08835 | V-web | G6 structural | **authors corrected** (bib listed Kudahl and Mikkelsen) |
| MianChowla1944 | A. M. Mian, S. Chowla, "On the B₂ sequences of Sidon," Proc. Nat. Acad. Sci. India A 14 (1944) 3–4 | V-web | G6 structural | volume/pages added |
| Rolnick | D. Rolnick, "On the classification of Stanley sequences," European J. Combin. 59 (2017) 51–70; arXiv:1408.1940 | V-web | G6 structural | published version added |
| BerlekampConwayGuy1982 | E. R. Berlekamp, J. H. Conway, R. K. Guy, *Winning Ways for your Mathematical Plays*, vol. 2, Academic Press, 1982 | V-ext | G7 calibration (p=1) | — |
| Conway1996 | J. H. Conway, "The angel problem," in *Games of No Chance*, MSRI Publ. 29, Cambridge UP, 1996, 3–12 | V-web | G7 calibration | publisher added |
| Bowditch2007 | B. H. Bowditch, "The angel game in the plane," Combin. Probab. Comput. 16(3) (2007) 345–362 | V-ext | G7 calibration (p=4) | — |
| Mathe2007 | A. Máthé, "The angel of power 2 wins," Combin. Probab. Comput. 16(3) (2007) 363–374 | V-ext | G7 calibration (p=2) | — |
| Kloster2007 | O. Kloster, "A solution to the angel problem," Theoret. Comput. Sci. 389(1–2) (2007) 152–161 | V-ext | G7 calibration (p=2) | — |
| Gacs2007 | P. Gács, "The angel wins," arXiv:0706.2817 (2007) | V-web | G7 calibration (high power) | year added |
| NowakowskiWinkler1983; AignerFromme1984; FraichardAsama2004 | Discrete Math. 43(2–3) (1983) 235–239; Discrete Appl. Math. 8(1) (1984) 1–12; Advanced Robotics 18(10) (2004) 1001–1024 (DOIs added) | V-web | G7 structural instantiations | DOIs added |
| BorodinEtAl2001; Grimmett1999; Kesten1982; LaValle2006 | as in bib (standard references, metadata consistent) | T | G7 structural instantiations | — |
| Dhar1990 | D. Dhar, Phys. Rev. Lett. 64(14) (1990) 1613–1616, DOI 10.1103/PhysRevLett.64.1613 | V-web | G8.A (RECOVERED STANDARD) | DOI added |
| FeyLevinePeres2010 | A. Fey, L. Levine, Y. Peres, "Growth rates and explosions in sandpiles," J. Stat. Phys. 138 (2010) 143–159, DOI 10.1007/s10955-009-9899-6; arXiv:0901.3805 | V-web, V-ext | G8.B canonical (this paper's version is weaker: legal-vs-legal) | entry type/DOI fixed |
| HolroydEtAl2008 | A. E. Holroyd et al., "Chip-firing and rotor-routing on directed graphs," in *In and Out of Equilibrium 2*, Progr. Probab. 60, Birkhäuser, 2008, 331–364 | V-web | G8 instantiation | publisher added |
| EisenbergNoe2001; Cybenko1989; BoydEtAl2006; BeggsPlenz2003 | Management Sci. 47(2) 236–249; JPDC 7(2) (1989) 279–301; IEEE TIT 52(6) (2006) 2508–2530 (DOI added); J. Neurosci. 23(35) (2003) 11167–11177 | V-ledger (Eisenberg–Noe); V-web (others) | G8 structural | DOI added (Boyd et al.) |
| Fuks1997; Nagel1996; ChowdhurySantenSchadschneider2000 | as in bib (PRE 55 R2081; PRE 53 4655; Phys. Rep. 329 199–329) | V-ext | G9 calibration | entry types fixed |
| Langton1986 | C. G. Langton, "Studying artificial life with cellular automata," Physica D 22 (1986) 120–149 | V-web | G9 conjectural instantiation | — |
| BunimovichTroubetzkoy1992 | L. A. Bunimovich, S. E. Troubetzkoy, J. Stat. Phys. 67(1–2) (1992) 289–302 | V-ledger | G9 nonclaim (ant unboundedness) | — |
| Greenberg1978 | J. M. Greenberg, S. P. Hastings, "Spatial patterns for discrete models of diffusion in excitable media," SIAM J. Appl. Math. 34(3) (1978) 515–523 | V-web | G9 structural | **coauthor Hastings added** |
| DurrettGriffeath | R. Durrett, D. Griffeath, "Asymptotic behavior of excitable cellular automata," Experiment. Math. 2(3) (1993) 183–208 | V-web | G9 structural | published version added |
| Gardner1970 | M. Gardner, "Mathematical Games: The fantastic combinations of John Conway's new solitaire game 'life'," Sci. Amer. 223(4) (Oct. 1970) 120–123 | V-web | G9 structural | volume/pages added |
| Pivato | M. Pivato, "Defect particle kinematics in one-dimensional cellular automata," Theoret. Comput. Sci. 377 (2007) 205–228, DOI 10.1016/j.tcs.2007.03.014 | V-web | G9 structural | published version added |
| LighthillWhitham1955; Richards1956; Daganzo1994 | Proc. R. Soc. A 229(1178) (1955) 317–345; Oper. Res. 4(1) (1956) 42–51 (DOI added); Transp. Res. B 28(4) (1994) 269–287 | V-web | G9 structural | DOI added (Richards) |
| ChamberlandThomas2004 | M. Chamberland, D. Thomas, "The N-number Ducci game," J. Difference Equ. Appl. 10(3) (2004) 339–342 | V-ext | G10 Ducci calibration | — |
| Breuer2007a | Florian Breuer, "Ducci sequences in higher dimensions," Integers 7 (2007) A24 | V-web | G10 Ducci | **given name corrected** (bib had "Felix"); article number added |
| Breuer2007b | F. Breuer, E. Lötter, B. van der Merwe, "Ducci-sequences and cyclotomic polynomials," Finite Fields Appl. 13(2) (2007) 293–304 | V-web | G10 Ducci | **authors completed** ("and others" removed) |
| Odlyzko1993 | A. M. Odlyzko, "Iterated absolute values of differences of consecutive primes," Math. Comp. 61(203) (1993) 373–380 | V-ledger | G10 Gilbreath | — |
| Chase2020 | Z. Chase, "A random analogue of Gilbreath's conjecture," Math. Ann. 388 (2024) 2611–2625; arXiv:2005.00530 | V-web | G10 Gilbreath | published version added |
| Plouffe2025 | S. Plouffe, "Verification of Gilbraith's conjecture up to 10^14" [sic, title as posted], arXiv:2510.06688 (2025) | V-web, V-ledger | G10 Gilbreath verification record | now cited in text (was uncited) |
| Strikwerda; GustafssonKreissOliger; CoulombelFaye | J. C. Strikwerda, 2nd ed., SIAM 2004; B. Gustafsson, H.-O. Kreiss, J. Oliger, 2nd ed., Wiley 2013; J.-F. Coulombel, G. Faye, IMA J. Numer. Anal. 43(1) (2023) 187–224, DOI 10.1093/imanum/drab088, arXiv:2102.03066 | T / T / V-web | G10 structural | editions/years; published version with pages and DOI |
| Canny1986; Witkin1983; Fletcher1982; StoneEtAl1998 | Canny IEEE TPAMI 8(6) 679–698 (DOI added); Witkin IJCAI-83, 1019–1022; Fletcher IEEE Trans. Commun. COM-30(1) (1982) 247–252; Stone et al. IEEE/ACM Trans. Netw. 6(5) (1998) 529–543 | V-web | G10 structural | pages/volumes/DOI added |
| Berger1966 | R. Berger, *The Undecidability of the Domino Problem*, Mem. Amer. Math. Soc. 66, AMS, 1966 | V-web | G11 calibration (RECOVERED STANDARD) | publisher added |
| Robinson1971 | R. M. Robinson, "Undecidability and nonperiodicity for tilings of the plane," Invent. Math. 12 (1971) 177–209 | V-ext | G11 (RECOVERED STANDARD: hierarchy proof) | — |
| Penrose1974 | R. Penrose, Bull. Inst. Math. Appl. 10 (1974) 266–271 | V-ext | G11 calibration | — |
| SmithEtAl2023Hat | D. Smith, J. S. Myers, C. S. Kaplan, C. Goodman-Strauss, "An aperiodic monotile," Combinatorial Theory 4(1) (2024) #6, DOI 10.5070/C64163843; arXiv:2303.10798 | V-web, V-ext | G11 calibration | published version added |
| SmithEtAl2023Spectre | same authors, "A chiral aperiodic monotile," Combinatorial Theory 4(2) (2024) #13, DOI 10.5070/C64264241; arXiv:2305.17743 | V-web, V-ext | G11 calibration | published version added |
| JeandelRao2021 (new) | E. Jeandel, M. Rao, "An aperiodic set of 11 Wang tiles," Advances in Combinatorics 2021:1, 37 pp., DOI 10.19086/aic.18614; arXiv:1506.06492 | V-web, V-ext | G11 lab exhibit (tile set used by G11-L1) | added (was cited nowhere) |
| ShechtmanEtAl1984 | D. Shechtman, I. Blech, D. Gratias, J. W. Cahn, Phys. Rev. Lett. 53(20) (1984) 1951–1954, DOI 10.1103/PhysRevLett.53.1951 | V-web | G11 instantiation | **end page corrected** (bib had 1953); DOI added |
| Senechal1995; LindMarcus1995; Dechter2003; HaeuplerShahrasbi2017 | as in bib (books; STOC pages verified) | T / V-web (Haeupler–Shahrasbi) | G11 instantiations | — |
| DurandRomashchenkoShen | B. Durand, A. Romashchenko, A. Shen, "Fixed point and aperiodic tilings," DLT 2008, LNCS 5257, 276–288; arXiv:0802.2432 | V-web | G11 instantiation | published version added |
| DeGrey2018 | A. D. N. J. de Grey, "The chromatic number of the plane is at least 5," Geombinatorics 28(1) (2018) 18–31; arXiv:1804.02385 | V-web | G12 calibration | **pages corrected** (bib had 5–18) |
| Heule2018 | M. J. H. Heule, "Computing small unit-distance graphs with chromatic number 5," Geombinatorics 28(1) (2018) 32–50; arXiv:1805.12181 | V-web | G12 calibration | published version added |
| Parts2020 | J. Parts, "Graph minimization, focusing on the example of 5-chromatic unit-distance graphs in the plane," Geombinatorics 29(4) (2020) 137–166; arXiv:2010.12665 | V-web, V-ledger | G12 calibration | entry type fixed |
| BruijnErdos1951 | N. G. de Bruijn, P. Erdős, "A colour problem for infinite graphs and a problem in the theory of relations," Indag. Math. 13 (1951) 369–373 (Proc. KNAW Ser. A 54) | V-web | G12.3 (RECOVERED STANDARD) | journal/pages added |
| ShelahSoifer2003 | S. Shelah, A. Soifer, J. Combin. Theory Ser. A 103 (2003) 387–391 | V-ledger | G12 choice-sensitivity | — |
| Falconer1981 | K. J. Falconer, "The realization of distances in measurable subsets covering ℝⁿ," J. Combin. Theory Ser. A 31(2) (1981) 184–189 | V-web | G12 measurable-coloring row | **pages corrected** (bib had 187–189) |
| GareyJohnsonStockmeyer1976; Laman1970; AsimowRoth1978; RobertsonSeymour2004; Gibbard1973; Satterthwaite1975 | TCS 1(3) (1976) 237–267; J. Eng. Math. 4(4) (1970) 331–340; Trans. AMS 245 (1978) 279–289; JCTB 92 (2004) 325–357; Econometrica 41(4) (1973) 587–601; J. Econ. Theory 10(2) (1975) 187–217 (DOIs and full titles added) | V-web | G12 structural | DOIs; Gibbard and Satterthwaite full titles |
| BourgainFuchs2010 | J. Bourgain, E. Fuchs, "A proof of the positive density conjecture for integer Apollonian circle packings," J. Amer. Math. Soc. 24 (2011) 945–967, DOI 10.1090/S0894-0347-2011-00707-8; arXiv:1001.3894 | V-web, V-ledger | G13 calibration | published version added |
| BourgainKontorovich2014Apollonian | Invent. Math. 196 (2014) 589–650 | V-ledger | G13 imported saturation (RECOVERED STANDARD) | — |
| HaagEtAl2024 | Ann. of Math. 200(2) (2024) 749–770; arXiv:2307.02749 | V-ledger | G13 reciprocity record (RECOVERED STANDARD) | — |
| BourgainKontorovich2014Zaremba | Ann. of Math. 180 (2014) 137–196 | V-ledger | G13 Zaremba instantiation | — |
| KontorovichOh2012; HooryLinialWigderson2006; BaakeGrimm2013 | Crelle 667 (2012) 89–131; Bull. AMS 43(4) (2006) 439–561; book | V-web / V-web / T | G13 instantiations | — |

## Mechanical record of every bibliography change (git diff of `paper/references.bib` against Phase 2 HEAD, field by field)

| Key | Change |
|---|---|
| AgrawalChatterjeeNovotny2017 | type misc→article; author: "Agrawal, Sourabh and Chatterjee, Krishnendu and Novotn\'y, Petr" → "Agrawal, Sheshansh and Chatterjee, Krishnendu and Novotn\'y, Petr"; +doi=10.1145/3158122; +journal=Proceedings of the ACM on Programming Languages; +number=POPL; +pages=34:1--34:32; +volume=2; year: "2017" → "2018" |
| AignerFromme1984 | +doi=10.1016/0166-218X(84)90073-8 |
| BellemareEtAl2016 | author: "Bellemare, Marc and Srinivasan, Sriram and Ostrovski, Georg and Schaul, Tom and Saxton, David and Munos, Remi" → "Bellemare, Marc G. and Srinivasan, Sriram and Ostrovski, Georg and Schaul, Tom and Saxton, David and Munos, R{\'e}mi"; booktitle: "NeurIPS" → "Advances in Neural Information Processing Systems 29 (NeurIPS 2016)" |
| Berger1966 | +publisher=American Mathematical Society |
| BourgainFuchs2010 | type misc→article; +doi=10.1090/S0894-0347-2011-00707-8; +journal=Journal of the American Mathematical Society; +number=4; +pages=945--967; title: "A proof of the positive density conjecture for integer Apollonian circle packings" → "A proof of the positive density conjecture for integer {Apollonian} circle packings"; +volume=24; +year=2011 |
| BoyarEtAl | type misc→article; author: "Boyar, Joan and Favrholdt, Lene M. and Kudahl, Christian and Mikkelsen, J{\o}rgen W." → "Boyar, Joan and Favrholdt, Lene M. and Kotrb{\v{c}}{\'i}k, Michal and Larsen, Kim S."; +journal=Algorithmica; note: "arXiv:1704.08835" → "Preliminary version in WADS 2017; arXiv:1704.08835"; +number=7; +pages=1916--1951; +volume=84; +year=2022 |
| BoydEtAl2006 | +doi=10.1109/TIT.2006.874516 |
| Breuer2007a | author: "Breuer, Felix" → "Breuer, Florian"; +pages=A24 |
| Breuer2007b | author: "Breuer, Felix and others" → "Breuer, Florian and L\"otter, Ernest and van der Merwe, Brink"; +number=2 |
| Brown-MathPages | note: "MathPages, \url{https://www.mathpages.com/home/kmath004/kmath004.htm}; informally sourced, no peer-reviewed publication located" → "MathPages, \url{https://www.mathpages.com/home/kmath004/kmath004.htm}, accessed 2026-09-02; informally sourced, no peer-reviewed publication located"; +year=2026 |
| BruijnErdos1951 | +journal=Indagationes Mathematicae; +note=Nederl. Akad. Wetensch. Proc. Ser. A 54; +pages=369--373; +volume=13 |
| Canny1986 | +doi=10.1109/TPAMI.1986.4767851; +number=6; volume: "8" → "PAMI-8" |
| ChamberlandThomas2004 | +doi=10.1080/10236190410001647807 |
| Chase2020 | type misc→article; +doi=10.1007/s00208-023-02579-w; +journal=Mathematische Annalen; +pages=2611--2625; title: "A random analogue of Gilbreath's conjecture" → "A random analogue of {Gilbreath}'s conjecture"; +volume=388; +year=2024 |
| ChowdhurySantenSchadschneider2000 | type misc→article |
| ClarkeEtAl2003 | +doi=10.1145/876638.876643 |
| Conway1996 | +publisher=Cambridge University Press |
| CormenEtAl | +year=2009 |
| CoulombelFaye | type misc→article; +doi=10.1093/imanum/drab088; +journal=IMA Journal of Numerical Analysis; +number=1; +pages=187--224; +volume=43; +year=2023 |
| DeGrey2018 | type misc→article; +number=1; pages: "5--18" → "18--31" |
| Dershowitz1982 | +doi=10.1016/0304-3975(82)90026-3 |
| DershowitzManna1979 | +doi=10.1145/359138.359142 |
| Dhar1990 | +doi=10.1103/PhysRevLett.64.1613; +number=14 |
| DurandRomashchenkoShen | type misc→inproceedings; +booktitle=Developments in Language Theory (DLT 2008); +pages=276--288; +publisher=Springer; +series=Lecture Notes in Computer Science; +volume=5257; +year=2008 |
| DurrettGriffeath | type misc→article; +journal=Experimental Mathematics; +number=3; +pages=183--208; +volume=2; +year=1993 |
| Eppstein1995 | +pages=5--15 |
| Falconer1981 | +number=2; pages: "187--189" → "184--189" |
| FeyLevinePeres2010 | type misc→article; +doi=10.1007/s10955-009-9899-6 |
| Fibonacci | type book→misc; +howpublished=Manuscript; English translation: L. E. Sigler, \emph{Fibonacci's Liber Abaci}, Springer, 2002; +year=1202 |
| Fletcher1982 | +number=1; +pages=247--252; +volume=COM-30 |
| FoundationsVCognition | +note=In preparation; not vendored in this paper's repository, cited by law name only |
| FraichardAsama2004 | +doi=10.1163/1568553042674662 |
| Fuks1997 | type misc→article |
| Gacs2007 | +year=2007 |
| Gardner1970 | +number=4; +pages=120--123; title: "Mathematical Games: The fantastic combinations of John Conway's new solitaire game Life" → "Mathematical Games: The fantastic combinations of {John Conway}'s new solitaire game ``Life''"; +volume=223 |
| GareyJohnsonStockmeyer1976 | +doi=10.1016/0304-3975(76)90059-1 |
| Gentzen1936 | +doi=10.1007/BF01565428 |
| Gibbard1973 | title: "Manipulation of voting schemes" → "Manipulation of voting schemes: a general result" |
| Greenberg1978 | author: "Greenberg, James M." → "Greenberg, James M. and Hastings, Stuart P."; +number=3 |
| GustafssonKreissOliger | +edition=2nd; title: "Time Dependent Problems and Difference Methods" → "Time-Dependent Problems and Difference Methods"; +year=2013 |
| GuyUnsolved | +year=2004 |
| HaeuplerShahrasbi2017 | booktitle: "STOC" → "Proceedings of the 49th Annual ACM SIGACT Symposium on Theory of Computing (STOC 2017)"; +pages=33--46; title: "Synchronization Strings: Codes for Insertions and Deletions Approaching the Singleton Bound" → "Synchronization Strings: Codes for Insertions and Deletions Approaching the {Singleton} Bound" |
| Heule2018 | type misc→article; +journal=Geombinatorics; +number=1; +pages=32--50; +volume=28 |
| HolroydEtAl2008 | +publisher=Birkh\"auser |
| JeandelRao2021 | **added** (article) |
| Kocher1996 | booktitle: "CRYPTO" → "Advances in Cryptology --- CRYPTO '96"; +pages=104--113; +publisher=Springer; +series=Lecture Notes in Computer Science; title: "Timing Attacks on Implementations of Diffie-Hellman, RSA, DSS, and Other Systems" → "Timing Attacks on Implementations of {Diffie-Hellman}, {RSA}, {DSS}, and Other Systems"; +volume=1109 |
| Lagarias1985 | +doi=10.2307/2322189; +number=1 |
| Laman1970 | +doi=10.1007/BF01534980 |
| MianChowla1944 | journal: "Proceedings of the National Academy of Sciences, India A" → "Proceedings of the National Academy of Sciences, India, Section A"; +pages=3--4; title: "On the B\_2 sequences of Sidon" → "On the {$B_2$} sequences of {Sidon}"; +volume=14 |
| Nagel1996 | type misc→article |
| NowakowskiWinkler1983 | +doi=10.1016/0012-365X(83)90160-7 |
| OEIS-A005132 | note: "The On-Line Encyclopedia of Integer Sequences, \url{https://oeis.org/A005132}" → "The On-Line Encyclopedia of Integer Sequences, \url{https://oeis.org/A005132}, accessed 2026-09-02"; +year=2026 |
| OEIS-A057167 | note: "The On-Line Encyclopedia of Integer Sequences, \url{https://oeis.org/A057167}" → "The On-Line Encyclopedia of Integer Sequences, \url{https://oeis.org/A057167}, accessed 2026-09-02"; +year=2026 |
| OEIS-A060382 | note: "The On-Line Encyclopedia of Integer Sequences, \url{https://oeis.org/A060382}" → "The On-Line Encyclopedia of Integer Sequences, \url{https://oeis.org/A060382}, accessed 2026-09-02"; +year=2026 |
| OzelEtAl | type misc→article; +journal=IEEE Journal on Selected Areas in Communications; +number=8; +pages=1732--1743; +volume=29; +year=2011 |
| Parts2020 | type misc→article |
| Pivato | type misc→article; +doi=10.1016/j.tcs.2007.03.014; +journal=Theoretical Computer Science; +number=1--3; +pages=205--228; +volume=377; +year=2007 |
| Richards1956 | +doi=10.1287/opre.4.1.42 |
| RobertsonSeymour2004 | +doi=10.1016/j.jctb.2004.08.001 |
| Robinson1971 | +doi=10.1007/BF01418780 |
| Rolnick | type misc→article; +journal=European Journal of Combinatorics; +pages=51--70; title: "On the classification of Stanley sequences" → "On the classification of {Stanley} sequences"; +volume=59; +year=2017 |
| Satterthwaite1975 | title: "Strategy-proofness and Arrow's conditions" → "Strategy-proofness and {Arrow}'s conditions: existence and correspondence theorems for voting procedures and social welfare functions" |
| ShechtmanEtAl1984 | +doi=10.1103/PhysRevLett.53.1951; +number=20; pages: "1951--1953" → "1951--1954" |
| SmithEtAl2023Hat | type misc→article; +doi=10.5070/C64163843; +journal=Combinatorial Theory; note: "arXiv:2303.10798; Combinatorial Theory, 2024" → "arXiv:2303.10798"; +number=1; +pages=\#6; +volume=4; year: "2023" → "2024" |
| SmithEtAl2023Spectre | type misc→article; +doi=10.5070/C64264241; +journal=Combinatorial Theory; note: "arXiv:2305.17743; Combinatorial Theory, 2024" → "arXiv:2305.17743"; +number=2; +pages=\#13; +volume=4; year: "2023" → "2024" |
| StoneEtAl1998 | +number=5 |
| Strikwerda | +edition=2nd; +year=2004 |
| Tao2019Collatz | type misc→article; +doi=10.1017/fmp.2022.8; +journal=Forum of Mathematics, Pi; +pages=e12; title: "Almost all orbits of the Collatz map attain almost bounded values" → "Almost all orbits of the {Collatz} map attain almost bounded values"; +volume=10; year: "2019" → "2022" |
| Tarjan1985 | +doi=10.1137/0606031 |
| Tsiokos2026AOR | +doi=10.5281/zenodo.20713664; title: "Audited Operational Realisability: A Closure Completion Reflection for Carriers with Audit Data" → "Audited Operational Realisability: A Closure-Completion Reflection for Carriers with Audit Data" |
| Tsiokos2026Adequacy | **removed** (uncited) |
| Tsiokos2026Currency | +doi=10.5281/zenodo.18926771; title: "To Spend a Stone with Six Birds: Currency, Constraint Duality, and Shadow Prices Across Closure Layers" → "To Spend a Stone with Six Birds: Currency--Constraint Duality and Shadow Prices Across Closure Layers" |
| Tsiokos2026EmergenceCalculus | +doi=10.5281/zenodo.18365949; title: "Six Birds Foundations of Emergence Calculus" → "Six Birds: Foundations of Emergence Calculus" |
| Tsiokos2026FoundII | +doi=10.5281/zenodo.19672278 |
| Tsiokos2026FoundIV | +doi=10.5281/zenodo.20713187 |
| Tsiokos2026Hiddenness | +doi=10.5281/zenodo.20713577 |
| Tsiokos2026NeedleKiller | +doi=10.5281/zenodo.20713688 |
| Tsiokos2026Rewriting | +doi=10.5281/zenodo.19061345; title: "To Flatten a Stone with Six Birds: Critical Pairs, Holonomy and Confluence in Rewriting Systems" → "To Flatten a Stone with Six Birds: Critical Pairs, Holonomy, and Confluence in Rewriting Systems" |
| Tsiokos2026WhyMath | +doi=10.5281/zenodo.20712761; note: "Twin edition: \emph{The Usefulness of Non-Descending Objects}; same theorem stack" → "Twin edition: \emph{The Usefulness of Non-Descending Objects: A Six Birds Theory of Mathematical Applicability}; same theorem stack" |
| Walker-Fourmilab | note: "Fourmilab; Lychrel-number survey references to Wade VanLandingham and later computation records" → "Fourmilab, \url{https://www.fourmilab.ch/documents/threeyears/}, accessed 2026-09-02"; title: "Three Years of Computing" → "Three Years Of Computing: Final Report On The Palindrome Quest"; +year=1990 |
| Willems1972 | +doi=10.1007/BF00276493 |
| Witkin1983 | booktitle: "IJCAI" → "Proceedings of the 8th International Joint Conference on Artificial Intelligence (IJCAI-83)"; +pages=1019--1022 |
| YangUlukus | type misc→article; +journal=IEEE Transactions on Communications; +number=1; +pages=220--230; +volume=60; +year=2012 |
