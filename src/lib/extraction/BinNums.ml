
type positive =
| Coq_xI of positive
| Coq_xO of positive
| Coq_xH

type coq_N =
| N0
| Npos of positive
