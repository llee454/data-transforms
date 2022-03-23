
val negb : bool -> bool



type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)



val existsb : ('a1 -> bool) -> 'a1 list -> bool

val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list

module type T =
 sig
  type t
 end

module Filter_unique :
 functor (M:T) ->
 functor (N:sig
  val is_same : M.t -> M.t -> bool
 end) ->
 sig
  type t = M.t

  val is_same : M.t -> M.t -> bool

  val is_unique : M.t list -> M.t -> bool

  val remove_not_unique : t list -> t list
 end

module Join :
 functor (A:T) ->
 functor (B:T) ->
 functor (N:sig
  val same_key : A.t -> B.t -> bool
 end) ->
 sig
  val join_aux : A.t -> B.t list -> (A.t*B.t) list

  val join : A.t list -> B.t list -> (A.t*B.t) list
 end

module Alist :
 functor (A:T) ->
 functor (K:T) ->
 functor (M:sig
  val is_same : A.t -> A.t -> bool

  val eq_dec : K.t -> K.t -> bool

  val val_key : A.t -> K.t
 end) ->
 sig
  val eq_dec : K.t -> K.t -> bool

  val eqb : K.t -> K.t -> bool

  type entry = K.t*A.t list

  val key : entry -> K.t

  val vals : entry -> A.t list

  val same_key : entry -> entry -> bool

  type alist = (K.t*A.t list) list

  val k_exists : alist -> K.t -> bool

  val k_existsb : alist -> K.t -> bool

  val insert : alist -> K.t -> A.t -> alist

  val group : A.t list -> alist
 end
