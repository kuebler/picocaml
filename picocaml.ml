external ps_add_clause: int list -> unit = "add_cls"
external ps_add_clauses: int list list -> unit = "add_clss"
external ps_get_clauses: unit -> int list list = "get_clauses"
external ps_init: unit -> unit = "ps_init"
external ps_reset: unit -> unit = "ps_reset"
external ps_sat: int -> int = "ps_sat"
external ps_unsat_core: int -> int list list = "ps_unsat_core"
external ps_get_model: unit -> int list = "ps_get_model"