
(** val negb : bool -> bool **)

let negb = Bool.not



type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)



(** val existsb : ('a1 -> bool) -> 'a1 list -> bool **)

let rec existsb = (fun f xs -> Core_kernel.List.exists xs ~f)

(** val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list **)

let rec filter = (fun f xs -> Core_kernel.List.filter xs ~f)

module type T =
 sig
  type t
 end

module Filter_unique =
 functor (M:T) ->
 functor (N:sig
  val is_same : M.t -> M.t -> bool
 end) ->
 struct
  type t = M.t

  (** val is_same : M.t -> M.t -> bool **)

  let is_same =
    N.is_same

  (** val is_unique : M.t list -> M.t -> bool **)

  let rec is_unique xs y =
    (fun branch0 branch1 xs ->
    match xs with
    | [] -> branch0 ()
    | x :: xs -> branch1 x xs)
      (fun _ -> true)
      (fun x xs0 ->
      (fun branch0 branch1 b ->
     match b with
     | true -> branch0 ()
     | false -> branch1 ())
        (fun _ -> negb (existsb (is_same y) xs0))
        (fun _ -> is_unique xs0 y)
        (is_same y x))
      xs

  (** val remove_not_unique : t list -> t list **)

  let rec remove_not_unique xs =
    (fun branch0 branch1 xs ->
    match xs with
    | [] -> branch0 ()
    | x :: xs -> branch1 x xs)
      (fun _ -> [])
      (fun x xs0 ->
      (fun branch0 branch1 b ->
     match b with
     | true -> branch0 ()
     | false -> branch1 ())
        (fun _ -> (fun (x, xs) -> List.cons x xs) (x,
        (remove_not_unique xs0)))
        (fun _ ->
        filter (fun y -> negb (is_same x y)) (remove_not_unique xs0))
        (is_unique ((fun (x, xs) -> List.cons x xs) (x, xs0)) x))
      xs
 end

module Join =
 functor (A:T) ->
 functor (B:T) ->
 functor (N:sig
  val same_key : A.t -> B.t -> bool
 end) ->
 struct
  (** val join_aux : A.t -> B.t list -> (A.t*B.t) list **)

  let rec join_aux x ys =
    (fun branch0 branch1 xs ->
    match xs with
    | [] -> branch0 ()
    | x :: xs -> branch1 x xs)
      (fun _ -> [])
      (fun y ys0 ->
      let zs = join_aux x ys0 in
      (fun branch0 branch1 b ->
     match b with
     | true -> branch0 ()
     | false -> branch1 ())
        (fun _ -> (fun (x, xs) -> List.cons x xs) ((x,y), zs))
        (fun _ -> zs)
        (N.same_key x y))
      ys

  (** val join : A.t list -> B.t list -> (A.t*B.t) list **)

  let rec join xs ys =
    (fun branch0 branch1 xs ->
    match xs with
    | [] -> branch0 ()
    | x :: xs -> branch1 x xs)
      (fun _ -> [])
      (fun x xs0 -> List.append (join_aux x ys) (join xs0 ys))
      xs
 end

module Alist =
 functor (A:T) ->
 functor (K:T) ->
 functor (M:sig
  val is_same : A.t -> A.t -> bool

  val eq_dec : K.t -> K.t -> bool

  val val_key : A.t -> K.t
 end) ->
 struct
  (** val eq_dec : K.t -> K.t -> bool **)

  let eq_dec =
    M.eq_dec

  (** val eqb : K.t -> K.t -> bool **)

  let eqb x y =
    if eq_dec x y then true else false

  type entry = K.t*A.t list

  (** val key : entry -> K.t **)

  let key =
    fst

  (** val vals : entry -> A.t list **)

  let vals =
    snd

  (** val same_key : entry -> entry -> bool **)

  let same_key xs ys =
    eqb (key xs) (key ys)

  type alist = (K.t*A.t list) list

  (** val k_exists : alist -> K.t -> bool **)

  let rec k_exists xss k =
    (fun branch0 branch1 xs ->
    match xs with
    | [] -> branch0 ()
    | x :: xs -> branch1 x xs)
      (fun _ -> false)
      (fun y l -> if eq_dec (key y) k then true else k_exists l k)
      xss

  (** val k_existsb : alist -> K.t -> bool **)

  let k_existsb xss k =
    if k_exists xss k then true else false

  (** val insert : alist -> K.t -> A.t -> alist **)

  let rec insert xss k x =
    (fun branch0 branch1 xs ->
    match xs with
    | [] -> branch0 ()
    | x :: xs -> branch1 x xs)
      (fun _ -> [])
      (fun y l ->
      if eq_dec (key y) k
      then let zs = (key y),((fun (x, xs) -> List.cons x xs) (x, (vals y))) in
           (fun (x, xs) -> List.cons x xs) (zs, (insert l k x))
      else (fun (x, xs) -> List.cons x xs) (y, (insert l k x)))
      xss

  (** val group : A.t list -> alist **)

  let rec group xs =
    (fun branch0 branch1 xs ->
    match xs with
    | [] -> branch0 ()
    | x :: xs -> branch1 x xs)
      (fun _ -> [])
      (fun x xs' ->
      let k = M.val_key x in
      let yss = group xs' in
      if k_exists yss k
      then insert yss k x
      else let zs = k,((fun (x, xs) -> List.cons x xs) (x, [])) in
           (fun (x, xs) -> List.cons x xs) (zs, yss))
      xs
 end
