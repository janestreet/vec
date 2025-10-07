open! Core
open Unboxed

module Arr_impl = struct
  open Uniform_array

  (* Safely exposes ['a t] as [mutable_data with 'a] even though
     [Obj.t Uniform_array.t] has kind [value]. *)
  type 'a t : mutable_data with 'a

  external wrap : Obj.t Uniform_array.t -> 'a t @@ portable = "%identity"
  external unwrap : 'a t -> Obj.t Uniform_array.t @@ portable = "%identity"

  let[@inline] length t = length (unwrap t)
  let[@inline] unsafe_clear_if_pointer t i = unsafe_clear_if_pointer (unwrap t) i

  let[@inline] unsafe_get (type a) (t : a t) i : a =
    unsafe_get (unwrap t) i |> Obj.Expert.obj
  ;;

  let[@inline] get_mono t i = get (unwrap t) i

  let[@inline always] unsafe_set (type a) (t : a t) i (element : a) =
    unsafe_set (unwrap t) i (Obj.repr element)
  ;;

  let[@inline] unsafe_set_int_assuming_currently_int t i int =
    unsafe_set_int_assuming_currently_int (unwrap t) i int
  ;;

  let[@inline] unsafe_blit ~src ~src_pos ~dst ~dst_pos ~len =
    unsafe_blit ~src:(unwrap src) ~src_pos ~dst:(unwrap dst) ~dst_pos ~len
  ;;

  let[@inline] sort ~pos ~len t ~compare = sort ~pos ~len (unwrap t) ~compare
  let[@inline] unsafe_create_uninitialized ~len = wrap (unsafe_create_uninitialized ~len)

  let[@inline] unsafe_to_array_inplace__promise_not_a_float t =
    unsafe_to_array_inplace__promise_not_a_float (unwrap t)
  ;;

  let[@inline] copy t = wrap (copy (unwrap t))

  let[@inline] init (type a) n ~(f : (int -> a) @ local) : a t =
    wrap (init n ~f:(fun i -> f i |> Obj.repr)) [@nontail]
  ;;
end

module Array = struct
  include Array

  let%template[@kind k = value] [@inline] unsafe_clear_if_pointer
    (type a : k)
    (t : a array)
    i
    =
    let e = unsafe_get t i in
    let e = Obj.repr e in
    if not (Obj.is_int e)
    then (
      let e : a = Obj.magic 0 in
      unsafe_set t i e)
  ;;

  let%template[@kind k = (value & value)] [@inline] unsafe_clear_if_pointer
    (type a : k)
    (t : a array)
    i
    =
    let e = unsafe_get t i in
    let #(a1, a2) : #(Obj.t * Obj.t) = Obj.magic e in
    if not (Obj.is_int a1 && Obj.is_int a2)
    then (
      let e : a = Obj.magic #(Obj.repr 0, Obj.repr 0) in
      unsafe_set t i e)
  ;;

  let%template[@kind k = (value & value & value)] [@inline] unsafe_clear_if_pointer
    (type a : k)
    (t : a array)
    i
    =
    let e = unsafe_get t i in
    let #(a1, a2, a3) : #(Obj.t * Obj.t * Obj.t) = Obj.magic e in
    if not (Obj.is_int a1 && Obj.is_int a2 && Obj.is_int a3)
    then (
      let e : a = Obj.magic #(Obj.repr 0, Obj.repr 0, Obj.repr 0) in
      unsafe_set t i e)
  ;;

  let%template[@kind k = (value & value & value & value)] [@inline] unsafe_clear_if_pointer
    (type a : k)
    (t : a array)
    i
    =
    let e = unsafe_get t i in
    let #(a1, a2, a3, a4) : #(Obj.t * Obj.t * Obj.t * Obj.t) = Obj.magic e in
    if not (Obj.is_int a1 && Obj.is_int a2 && Obj.is_int a3 && Obj.is_int a4)
    then (
      let e : a = Obj.magic #(Obj.repr 0, Obj.repr 0, Obj.repr 0, Obj.repr 0) in
      unsafe_set t i e)
  ;;

  let%template[@kind k = immediate64] [@inline] unsafe_clear_if_pointer
    (type a : k)
    (t : a array)
    i
    =
    match Base.Int63.Private.repr with
    | Int -> ()
    | Int64 -> (unsafe_clear_if_pointer [@kind value]) t i
  ;;

  let%template[@kind k = (immediate64 & immediate64)] [@inline] unsafe_clear_if_pointer
    (type a : k)
    (t : a array)
    i
    =
    match Base.Int63.Private.repr with
    | Int -> ()
    | Int64 -> (unsafe_clear_if_pointer [@kind value & value]) t i
  ;;

  let%template[@kind k = (immediate64 & immediate64 & immediate64)] [@inline] unsafe_clear_if_pointer
    (type a : k)
    (t : a array)
    i
    =
    match Base.Int63.Private.repr with
    | Int -> ()
    | Int64 -> (unsafe_clear_if_pointer [@kind value & value & value]) t i
  ;;

  let%template[@kind k = (immediate64 & immediate64 & immediate64 & immediate64)]
              [@inline] unsafe_clear_if_pointer
    (type a : k)
    (t : a array)
    i
    =
    match Base.Int63.Private.repr with
    | Int -> ()
    | Int64 -> (unsafe_clear_if_pointer [@kind value & value & value & value]) t i
  ;;

  let%template[@kind k = (value & value, immediate64 & immediate64)] unsafe_create_uninitialized
    (type a : k)
    ~len
    : a t
    =
    let v : a = Obj.magic #(0, 0) in
    create ~len v
  ;;

  let%template[@kind k = (value & value & value, immediate64 & immediate64 & immediate64)] unsafe_create_uninitialized
    (type a : k)
    ~len
    : a t
    =
    let v : a = Obj.magic #(0, 0, 0) in
    create ~len v
  ;;

  let%template[@kind
                k
                = ( value & value & value & value
                  , immediate64 & immediate64 & immediate64 & immediate64 )] unsafe_create_uninitialized
    (type a : k)
    ~len
    : a t
    =
    let v : a = Obj.magic #(0, 0, 0, 0) in
    create ~len v
  ;;

  let%template[@kind k = immediate64] unsafe_create_uninitialized (type a : k) ~len : a t =
    let v : a = Obj.magic 0 in
    create ~len v
  ;;
end

module%template
  [@kind
    k
    = ( immediate64
      , value & value
      , immediate64 & immediate64
      , value & value & value
      , immediate64 & immediate64 & immediate64
      , value & value & value & value
      , immediate64 & immediate64 & immediate64 & immediate64 )] Arr_impl =
struct
  open Array

  type ('a : k) t = 'a Array.t

  let[@inline] unsafe_create_uninitialized ~len =
    (unsafe_create_uninitialized [@kind k]) ~len
  ;;

  let init len ~f =
    let t = (unsafe_create_uninitialized [@kind k]) ~len in
    for i = 0 to len - 1 do
      unsafe_set t i (f i)
    done;
    t
  ;;

  let[@inline] unsafe_get (t : _ t) i = unsafe_get t i
  let[@inline] unsafe_set (t : _ t) i e = unsafe_set t i e

  let unsafe_blit ~(src : _ t) ~src_pos ~(dst : _ t) ~dst_pos ~len =
    let blit_one i = unsafe_set dst (dst_pos + i) (unsafe_get src (src_pos + i)) in
    if phys_equal src dst && src_pos < dst_pos
    then
      for i = len - 1 downto 0 do
        (blit_one [@inlined]) i
      done
    else
      for i = 0 to len - 1 do
        (blit_one [@inlined]) i
      done
  ;;

  let copy t =
    let t' = (unsafe_create_uninitialized [@kind k]) ~len:(length t) in
    unsafe_blit ~src:t ~src_pos:0 ~dst:t' ~dst_pos:0 ~len:(length t);
    t'
  ;;

  let[@inline] length t = length t
  let get_mono = get

  let[@inline] unsafe_clear_if_pointer (t : _ t) i =
    (unsafe_clear_if_pointer [@kind k]) t i
  ;;
end

module%template [@kind bits64] Arr_impl = struct
  include I64.Array

  type ('a : bits64) t = 'a I64.Array.t

  let get_mono = get

  let[@inline] unsafe_create_uninitialized (type a : bits64) ~len : a t =
    unsafe_create_uninitialized ~len
  ;;
end

module%template [@kind float32] Arr_impl = struct
  include F32.Array

  type ('a : float32) t = 'a F32.Array.t

  let get_mono = get

  let[@inline] unsafe_create_uninitialized (type a : float32) ~len : a t =
    unsafe_create_uninitialized ~len
  ;;
end

[%%template
[@@@kind.default
  k
  = ( value
    , immediate64
    , value & value
    , immediate64 & immediate64
    , value & value & value
    , immediate64 & immediate64 & immediate64
    , value & value & value & value
    , immediate64 & immediate64 & immediate64 & immediate64
    , float32
    , bits64 )]

open Arr_impl [@kind k]

type 'a arr_impl = 'a t]

external magic_32 : ('a : float32) -> ('b : float32) @@ portable = "%identity"
external magic_64 : ('a : bits64) -> ('b : bits64) @@ portable = "%identity"

let sexp_of_out_of_range_element (type a) (a : a) =
  let imm : int = Obj.magic a in
  Sexp.Atom (sprintf "_%d" imm)
;;

let%template[@kind k = (value & value)] sexp_of_out_of_range_element (type a : k) (a : a) =
  let #(imm1, imm2) : #(int * int) = Obj.magic a in
  Sexp.Atom (sprintf "(_%d, _%d)" imm1 imm2)
;;

let%template[@kind k = (value & value & value)] sexp_of_out_of_range_element
  (type a : k)
  (a : a)
  =
  let #(imm1, imm2, imm3) : #(int * int * int) = Obj.magic a in
  Sexp.Atom (sprintf "(_%d, _%d, _%d)" imm1 imm2 imm3)
;;

let%template[@kind k = (value & value & value & value)] sexp_of_out_of_range_element
  (type a : k)
  (a : a)
  =
  let #(imm1, imm2, imm3, imm4) : #(int * int * int * int) = Obj.magic a in
  Sexp.Atom (sprintf "(_%d, _%d, _%d, _%d)" imm1 imm2 imm3 imm4)
;;

let%template[@kind k = (immediate64 & immediate64)] [@inline] sexp_of_out_of_range_element
  (type a : k)
  (a : a)
  =
  (sexp_of_out_of_range_element [@kind value & value]) a
;;

let%template[@kind k = immediate64] [@inline] sexp_of_out_of_range_element
  (type a : k)
  (a : a)
  =
  (sexp_of_out_of_range_element [@kind value]) a
;;

let%template[@kind k = (immediate64 & immediate64 & immediate64)] [@inline] sexp_of_out_of_range_element
  (type a : k)
  (a : a)
  =
  (sexp_of_out_of_range_element [@kind value & value & value]) a
;;

let%template[@kind k = (immediate64 & immediate64 & immediate64 & immediate64)] [@inline] sexp_of_out_of_range_element
  (type a : k)
  (a : a)
  =
  (sexp_of_out_of_range_element [@kind value & value & value & value]) a
;;

let%template[@kind float32] sexp_of_out_of_range_element (type a : float32) (a : a) =
  let imm : float32# = magic_32 a in
  Sexp.Atom [%string "_%{imm#F32}"]
;;

let%template[@kind bits64] sexp_of_out_of_range_element (type a : bits64) (a : a) =
  let imm : i64 = magic_64 a in
  Sexp.Atom [%string "_%{imm#I64}"]
;;

let out_of_range_invariant (type a : value) (element : a) =
  assert (Obj.repr element |> Obj.is_int)
;;

let%template[@kind k = (value & value)] out_of_range_invariant (type a : k) (e : a) =
  let #(a1, a2) : #(Obj.t * Obj.t) = Obj.magic e in
  out_of_range_invariant a1;
  out_of_range_invariant a2
;;

let%template[@kind k = (value & value & value)] out_of_range_invariant
  (type a : k)
  (e : a)
  =
  let #(a1, a2, a3) : #(Obj.t * Obj.t * Obj.t) = Obj.magic e in
  out_of_range_invariant a1;
  out_of_range_invariant a2;
  out_of_range_invariant a3
;;

let%template[@kind k = (value & value & value & value)] out_of_range_invariant
  (type a : k)
  (e : a)
  =
  let #(a1, a2, a3, a4) : #(Obj.t * Obj.t * Obj.t * Obj.t) = Obj.magic e in
  out_of_range_invariant a1;
  out_of_range_invariant a2;
  out_of_range_invariant a3;
  out_of_range_invariant a4
;;

let%template[@kind k = immediate64] [@inline] out_of_range_invariant (type a : k) (e : a) =
  (out_of_range_invariant [@kind value]) e
;;

let%template[@kind k = (immediate64 & immediate64)] [@inline] out_of_range_invariant
  (type a : k)
  (e : a)
  =
  (out_of_range_invariant [@kind value & value]) e
;;

let%template[@kind k = (immediate64 & immediate64 & immediate64)] [@inline] out_of_range_invariant
  (type a : k)
  (e : a)
  =
  (out_of_range_invariant [@kind value & value & value]) e
;;

let%template[@kind k = (immediate64 & immediate64 & immediate64 & immediate64)] [@inline] out_of_range_invariant
  (type a : k)
  (e : a)
  =
  (out_of_range_invariant [@kind value & value & value & value]) e
;;

let%template[@kind float32] out_of_range_invariant _element = ()
let%template[@kind bits64] out_of_range_invariant _element = ()

module With_integer_index = struct
  (* Kernel hides away Obj-handling. *)

  module Kernel : sig @@ portable
    [%%template:
    [@@@kind.default
      k
      = ( float32
        , bits64
        , immediate64
        , value & value
        , immediate64 & immediate64
        , value & value & value
        , immediate64 & immediate64 & immediate64
        , value & value & value & value
        , immediate64 & immediate64 & immediate64 & immediate64
        , value )]

    type ('a : k) t : mutable_data with 'a

    val length : local_ (_ t[@kind k]) -> int [@@zero_alloc]
    val capacity : (_ t[@kind k]) -> int [@@zero_alloc]
    val create : ?initial_capacity:int -> unit -> (_ t[@kind k])
    val unsafe_create_uninitialized : len:int -> ('a t[@kind k])
    val init : int -> f:local_ (int -> 'a) -> ('a t[@kind k])
    val unsafe_get : ('a t[@kind k]) @ m -> int -> 'a [@@mode m = (local, global)]
    val unsafe_set : ('a t[@kind k]) -> int -> 'a -> unit

    val unsafe_blit
      :  src:local_ ('a t[@kind k])
      -> src_pos:int
      -> dst:local_ ('a t[@kind k])
      -> dst_pos:int
      -> len:int
      -> unit

    val max_index : (_ t[@kind k]) -> int
    val grow_capacity_once : (_ t[@kind k]) -> unit
    val grow_capacity_to_at_least : (_ t[@kind k]) -> capacity:int -> unit
    val unsafe_clear_pointer_at : (_ t[@kind k]) -> int -> unit
    val unsafe_set_length : (_ t[@kind k]) -> int -> unit
    val copy : ('a t[@kind k]) -> ('a t[@kind k])
    val invariant : ('a -> unit) -> ('a t[@kind k]) Invariant.t]

    module With_structure_details : sig
      type%template nonrec 'a t = ('a t[@kind k])
      [@@deriving sexp_of]
      [@@kind
        k
        = ( float32
          , bits64
          , value
          , immediate64
          , value & value
          , immediate64 & immediate64
          , value & value & value
          , immediate64 & immediate64 & immediate64
          , value & value & value & value
          , immediate64 & immediate64 & immediate64 & immediate64 )]
    end

    val unsafe_set_imm : ('a : immediate64). 'a t -> int -> 'a -> unit

    module Expert : sig
      val%template unsafe_inner : ('a t[@kind k]) -> ('a arr_impl[@kind k])
      [@@kind k = (float32, bits64, value)]
    end

    val sort : ?pos:int -> ?len:int -> 'a t -> compare:('a -> 'a -> int) -> unit
  end = struct
    [%%template
    [@@@kind.default
      k
      = ( float32
        , bits64
        , value
        , immediate64
        , value & value
        , immediate64 & immediate64
        , value & value & value
        , immediate64 & immediate64 & immediate64
        , value & value & value & value
        , immediate64 & immediate64 & immediate64 & immediate64 )]

    module [@kind] Arr = Arr_impl [@kind k]

    type ('a : k) t =
      { mutable arr : 'a Arr.t
      ; mutable length : int
      ; mutable capacity : int
      (** Invariant: [capacity = Arr.length arr]. We maintain it here to eliminate an
          indirection when accessing long arrays. *)
      }

    let unsafe_set_length t len = t.length <- len
    let capacity t = t.capacity
    let length t = t.length

    let[@kind] check_capacity capacity =
      if capacity < 0 then invalid_argf "Vec: negative capacity %d" capacity ()
    ;;

    (* [initial_capacity] is mostly arbitrary, but it does make our array take one header
       word + 7 data words = 8 words * 8 bytes = 64 bytes = one cacheline by default. (Of
       course, there's no alignment guarantee.) *)
    let create ?(initial_capacity = 7) () =
      check_capacity initial_capacity;
      { arr = Arr.unsafe_create_uninitialized ~len:initial_capacity
      ; length = 0
      ; capacity = initial_capacity
      }
    ;;

    let unsafe_create_uninitialized ~len:n =
      check_capacity n;
      { arr = Arr.unsafe_create_uninitialized ~len:n; length = n; capacity = n }
    ;;

    let init n ~f =
      check_capacity n;
      { arr = Arr.init n ~f; length = n; capacity = n }
    ;;

    let copy t = { arr = Arr.copy t.arr; length = t.length; capacity = t.capacity }

    let[@inline always] unsafe_get (type a : k) (t : (a t[@kind k])) i : a =
      Arr.unsafe_get t.arr i
    [@@mode m = (local, global)]
    ;;

    let[@inline always] unsafe_set (type a : k) (t : (a t[@kind k])) i (element : a) =
      Arr.unsafe_set t.arr i element
    ;;

    let[@inline always] unsafe_blit ~src ~src_pos ~dst ~dst_pos ~len =
      Arr.unsafe_blit ~src:src.arr ~src_pos ~dst:dst.arr ~dst_pos ~len
    ;;

    let[@inline always] max_index t = t.length - 1

    let grow_capacity_to_exactly t ~capacity =
      let arr = Arr.unsafe_create_uninitialized ~len:capacity in
      for i = 0 to (max_index [@kind k]) t do
        Arr.unsafe_set arr i (Arr.unsafe_get t.arr i)
      done;
      t.arr <- arr;
      t.capacity <- capacity
    ;;

    let[@kind] growth_factor = 2

    let grow_capacity_once t =
      (grow_capacity_to_exactly [@kind k])
        t
        ~capacity:(Int.max 1 t.capacity * growth_factor)
    ;;

    let grow_capacity_to_at_least t ~capacity:target_capacity =
      assert (growth_factor = 2);
      if t.capacity < target_capacity
      then
        (grow_capacity_to_exactly [@kind k])
          t
          ~capacity:(Int.ceil_pow2 (Int.max 1 target_capacity))
    ;;]

    module With_structure_details = struct
      [%%template
      [@@@kind.default
        k
        = ( float32
          , bits64
          , value
          , immediate64
          , value & value
          , immediate64 & immediate64
          , value & value & value
          , immediate64 & immediate64 & immediate64
          , value & value & value & value
          , immediate64 & immediate64 & immediate64 & immediate64 )]

      type nonrec 'a t = ('a t[@kind k])

      let sexp_of_t (type a : k) (sexp_of_a : a -> Sexp.t) (t : (a t[@kind k])) =
        let { arr; length; capacity } : (_ t[@kind k]) = t in
        let module Arr = Arr_impl [@kind k] in
        let elements =
          Uniform_array.init (Arr.length arr) ~f:(fun i ->
            let element = Arr.unsafe_get arr i in
            (* Only the first [length] elements can safely be given to [sexp_of_a]. *)
            if i < length
            then element |> sexp_of_a
            else element |> (sexp_of_out_of_range_element [@kind k]))
        in
        [%sexp { elements : Sexp.t Uniform_array.t; length : int; capacity : int }]
      ;;]
    end

    let%template[@kind
                  k
                  = ( float32
                    , bits64
                    , value
                    , immediate64
                    , value & value
                    , immediate64 & immediate64
                    , value & value & value
                    , immediate64 & immediate64 & immediate64
                    , value & value & value & value
                    , immediate64 & immediate64 & immediate64 & immediate64 )] invariant
      (type a : k)
      (a_inv : a -> unit)
      (t : (a t[@kind k]))
      =
      Invariant.invariant t [%sexp_of: (_ With_structure_details.t[@kind k])] (fun () ->
        let module Arr = Arr_impl [@kind k] in
        let { capacity; length; arr } : (_ t[@kind k]) = t in
        if capacity <> Arr.length t.arr
        then
          raise_s
            [%message
              "capacity should equal Option_array length"
                (capacity : int)
                (Arr.length t.arr : int)];
        if capacity < 0 then raise_s [%message "negative capacity" (capacity : int)];
        if length > capacity
        then
          raise_s
            [%message
              "length shouldn't be more than capacity" (length : int) (capacity : int)];
        for pos = 0 to length - 1 do
          a_inv (Arr.unsafe_get arr pos)
        done;
        for pos = length to capacity - 1 do
          Arr.get_mono arr pos |> (out_of_range_invariant [@kind k])
        done)
    ;;

    let[@inline always] unsafe_clear_pointer_at (t : _ t) pos =
      Arr_impl.unsafe_clear_if_pointer t.arr pos
    ;;

    let%template[@inline always]
                [@kind
                  k
                  = ( immediate64
                    , value & value
                    , immediate64 & immediate64
                    , value & value & value
                    , immediate64 & immediate64 & immediate64
                    , value & value & value & value
                    , immediate64 & immediate64 & immediate64 & immediate64 )] unsafe_clear_pointer_at
      (t : (_ t[@kind k]))
      pos
      =
      let module Arr_impl = Arr_impl [@kind k] in
      Arr_impl.unsafe_clear_if_pointer t.arr pos
    ;;

    let%template[@inline always] [@kind float32] unsafe_clear_pointer_at
      (_ : (_ t[@kind float32]))
      _
      : unit
      =
      ()
    ;;

    let%template[@inline always] [@kind bits64] unsafe_clear_pointer_at
      (_ : (_ t[@kind bits64]))
      _
      : unit
      =
      ()
    ;;

    module Arr = Arr_impl

    let sort (type a) ?pos ?len t ~(compare : a -> a -> int) =
      let compare : Obj.t -> Obj.t -> int = Obj.magic compare in
      (* [Uniform_array] checks this but has an overestimate of our length. *)
      let pos, len =
        Ordered_collection_common.get_pos_len_exn () ?pos ?len ~total_length:(length t)
      in
      Arr.sort ~pos ~len t.arr ~compare
    ;;

    module Expert = struct
      [%%template
      [@@@kind.default k = (float32, bits64, value)]

      let[@inline always] unsafe_inner (t : (_ t[@kind k])) = t.arr]
    end

    let[@inline always] unsafe_set_imm (type a : immediate64) (t : a t) i (element : a) =
      Arr.unsafe_set_int_assuming_currently_int t.arr i (Obj.magic element)
    ;;
  end

  include Kernel

  [%%template
  [@@@kind.default
    k
    = ( float32
      , bits64
      , value
      , immediate64
      , value & value
      , immediate64 & immediate64
      , value & value & value
      , immediate64 & immediate64 & immediate64
      , value & value & value & value
      , immediate64 & immediate64 & immediate64 & immediate64 )]

  let is_sorted t ~compare =
    (* This is a copy-paste from [Array.is_sorted]. *)
    let i = ref ((length [@kind k]) t - 1) in
    let result = ref true in
    while !i > 0 && !result do
      let elt_i = (unsafe_get [@kind k]) t !i in
      let elt_i_minus_1 = (unsafe_get [@kind k]) t (!i - 1) in
      if compare elt_i_minus_1 elt_i > 0 then result := false;
      decr i
    done;
    !result
  ;;

  let is_sorted_strictly t ~compare =
    (* This is a copy-paste from [Array.is_sorted_strictly]. *)
    let i = ref ((length [@kind k]) t - 1) in
    let result = ref true in
    while !i > 0 && !result do
      let elt_i = (unsafe_get [@kind k]) t !i in
      let elt_i_minus_1 = (unsafe_get [@kind k]) t (!i - 1) in
      if compare elt_i_minus_1 elt_i >= 0 then result := false;
      decr i
    done;
    !result
  ;;]

  include%template Binary_searchable.Make1 [@modality portable] (struct
      type nonrec 'a t = 'a t

      let length = length
      let get = unsafe_get
    end)

  [%%template
  [@@@kind.default
    k
    = ( float32
      , bits64
      , value
      , immediate64
      , value & value
      , immediate64 & immediate64
      , value & value & value
      , immediate64 & immediate64 & immediate64
      , value & value & value & value
      , immediate64 & immediate64 & immediate64 & immediate64 )]

  let next_free_index = (length [@kind k])

  let[@cold] raise__bad_index (t : (_ t[@kind k])) i ~op : unit =
    match
      raise_s
        [%message
          "tried to access vec out of bounds"
            (t : (_ With_structure_details.t[@kind k]))
            (i : int)
            (op : string)]
    with
    | (_ : Nothing.t) -> .
  ;;

  (* Tailcalls to raising functions are to be avoided, as the stack traces are much worse.
     Instead, we try really hard to inline wrapper functions that just perform non-tail
     calls to the raising functions.
  *)
  let[@inline always] raise__bad_index t i ~op : unit =
    (raise__bad_index [@kind k]) t i ~op [@nontail]
  ;;

  let[@inline always] check_index t i ~op =
    if i < 0 || i >= (length [@kind k]) t then (raise__bad_index [@kind k]) t i ~op
  ;;

  let get (type a : k) (t : (a t[@kind k])) i : a =
    (check_index [@kind k]) t i ~op:"get";
    (unsafe_get [@kind k]) t i
  ;;

  let set t i element =
    (check_index [@kind k]) t i ~op:"set";
    (unsafe_set [@kind k]) t i element
  ;;]

  let maybe_get t i = if i < 0 || i >= length t then None else Some (unsafe_get t i)

  let maybe_get_local t i =
    if i < 0 || i >= length t then None else exclave_ Some { global = unsafe_get t i }
  ;;

  let maybe_get_or_null t i =
    if i < 0 || i >= length t then Null else This (unsafe_get t i)
  ;;

  let set_imm (type a : immediate64) (t : a t) i (element : a) : unit =
    check_index t i ~op:"set_imm";
    unsafe_set_imm t i element
  ;;

  [%%template
  [@@@kind.default
    k
    = ( float32
      , bits64
      , value
      , immediate64
      , value & value
      , immediate64 & immediate64
      , value & value & value
      , immediate64 & immediate64 & immediate64
      , value & value & value & value
      , immediate64 & immediate64 & immediate64 & immediate64 )]

  let[@inline always] push_back__we_know_we_have_space t element =
    let length = (length [@kind k]) t in
    (unsafe_set [@kind k]) t length element;
    (unsafe_set_length [@kind k]) t (length + 1)
  ;;

  let push_back_index t element =
    let length = (length [@kind k]) t in
    if length = (capacity [@kind k]) t then (grow_capacity_once [@kind k]) t;
    (push_back__we_know_we_have_space [@kind k]) t element;
    length
  ;;

  let[@inline always] push_back t element =
    let (_ : int) = (push_back_index [@kind k]) t element in
    ()
  ;;]

  let[@inline always] push_back__we_know_we_have_space_imm t element =
    let length = length t in
    unsafe_set_imm t length element;
    unsafe_set_length t (length + 1)
  ;;

  let push_back_index_imm t element =
    let length = length t in
    if length = capacity t then grow_capacity_once t;
    push_back__we_know_we_have_space_imm t element;
    length
  ;;

  let[@inline always] push_back_imm t element =
    let (_ : int) = push_back_index_imm t element in
    ()
  ;;

  [%%template
  [@@@kind.default
    k
    = ( float32
      , bits64
      , value
      , immediate64
      , value & value
      , immediate64 & immediate64
      , value & value & value
      , immediate64 & immediate64 & immediate64
      , value & value & value & value
      , immediate64 & immediate64 & immediate64 & immediate64 )]

  let remove_exn t i =
    if i < 0 || i >= (length [@kind k]) t
    then (raise__bad_index [@kind k]) t i ~op:"remove_exn";
    let new_length = (length [@kind k]) t - 1 in
    (* As per the ocaml stdlib documentation, blitting with src and dst
       overlapping is safe.
       https://github.com/ocaml-flambda/flambda-backend/blob/main/ocaml/stdlib/array.mli#L143
    *)
    (unsafe_blit [@kind k])
      ~src:t
      ~src_pos:(i + 1)
      ~dst:t
      ~dst_pos:i
      ~len:((length [@kind k]) t - i - 1);
    (unsafe_set_length [@kind k]) t new_length
  ;;

  let[@inline always] unsafe_peek_back_exn t =
    (unsafe_get [@kind k]) t ((max_index [@kind k]) t)
  ;;

  let peek_back_exn t =
    let length = (length [@kind k]) t in
    if length <= 0 then (raise__bad_index [@kind k]) t length ~op:"peek_back";
    (unsafe_peek_back_exn [@kind k]) t
  ;;]

  let peek_back t = if length t <= 0 then None else Some (unsafe_peek_back_exn t)

  let[@inline always] pop_back_unit_imm_exn (type a : immediate64) (t : a t) =
    let pos = max_index t in
    if pos < 0 then raise__bad_index t (length t) ~op:"pop_back_unit_imm_exn";
    unsafe_set_length t pos
  ;;

  let pop_back_imm_exn t =
    let e = peek_back_exn t in
    pop_back_unit_imm_exn t;
    e
  ;;

  [%%template
  [@@@kind.default
    k
    = ( float32
      , bits64
      , value
      , immediate64
      , value & value
      , immediate64 & immediate64
      , value & value & value
      , immediate64 & immediate64 & immediate64
      , value & value & value & value
      , immediate64 & immediate64 & immediate64 & immediate64 )]

  let[@inline always] pop_back_unit_exn t =
    let pos = (max_index [@kind k]) t in
    if pos < 0
    then (raise__bad_index [@kind k]) t ((length [@kind k]) t) ~op:"pop_back_unit_exn";
    (* Don't leak the value. *)
    (unsafe_clear_pointer_at [@kind k]) t pos;
    (unsafe_set_length [@kind k]) t pos
  ;;

  let pop_back_exn t =
    let e = (peek_back_exn [@kind k]) t in
    (pop_back_unit_exn [@kind k]) t;
    e
  ;;

  let[@inline never] grow_to_unchecked t ~len ~default =
    (grow_capacity_to_at_least [@kind k]) t ~capacity:len;
    for i = (length [@kind k]) t to len - 1 do
      (unsafe_set [@kind k]) t i default
    done;
    (unsafe_set_length [@kind k]) t len
  ;;

  let[@inline always] grow_to t ~len ~default =
    if len > (length [@kind k]) t then (grow_to_unchecked [@kind k]) t ~len ~default
  ;;

  let grow_to_include t idx ~default = (grow_to [@kind k]) t ~len:(idx + 1) ~default

  let grow_to' t ~len ~default =
    if len > (length [@kind k]) t
    then (
      (grow_capacity_to_at_least [@kind k]) t ~capacity:len;
      for i = (length [@kind k]) t to len - 1 do
        (unsafe_set [@kind k]) t i (default i)
      done;
      (unsafe_set_length [@kind k]) t len)
  ;;

  let grow_to_include' t idx ~default = (grow_to' [@kind k]) t ~len:(idx + 1) ~default

  let shrink_to t ~len =
    if len < 0
    then (raise__bad_index [@kind k]) t len ~op:"shrink_to"
    else if len < (length [@kind k]) t
    then (
      for i = len to (max_index [@kind k]) t do
        (unsafe_clear_pointer_at [@kind k]) t i
      done;
      (unsafe_set_length [@kind k]) t len)
  ;;]

  let shrink_to_imm (type a : immediate64) (t : a t) ~len =
    if len < 0
    then raise__bad_index t len ~op:"shrink_to_imm"
    else if len < length t
    then unsafe_set_length t len
  ;;

  [%%template
  [@@@kind.default
    k
    = ( float32
      , bits64
      , value
      , immediate64
      , value & value
      , immediate64 & immediate64
      , value & value & value
      , immediate64 & immediate64 & immediate64
      , value & value & value & value
      , immediate64 & immediate64 & immediate64 & immediate64 )]

  let iteri t ~f =
    for i = 0 to (max_index [@kind k]) t do
      f i ((unsafe_get [@kind k]) t i)
    done
  ;;

  let iter t ~f =
    for i = 0 to (max_index [@kind k]) t do
      f ((unsafe_get [@kind k]) t i)
    done
  ;;]

  let rec iter_until' t ~f ~finish ~max_index i =
    if i > max_index
    then finish ()
    else (
      match (f (unsafe_get t i) : _ Continue_or_stop.t) with
      | Stop s -> s
      | Continue () -> iter_until' t ~f ~finish ~max_index (i + 1))
  ;;

  let iter_until t ~f ~finish = iter_until' t ~f ~finish ~max_index:(max_index t) 0

  let to_list t =
    let result = ref [] in
    for i = max_index t downto 0 do
      result := unsafe_get t i :: !result
    done;
    !result
  ;;

  let to_local_list t = exclave_
    let rec aux t i acc = exclave_
      if i < 0 then acc else aux t (i - 1) (unsafe_get t i :: acc)
    in
    aux t (max_index t) []
  ;;

  external unsafe_array_sub
    :  local_ Obj.t array
    -> int
    -> int
    -> local_ 'a iarray
    @@ portable
    = "caml_array_sub_local"

  external unsafe_iarray_of_array__promise_no_mutation
    : 'a.
    ('a array[@local_opt]) -> ('a iarray[@local_opt])
    @@ portable
    = "%array_to_iarray"

  let float_arrays_are_flat = Obj.tag (Obj.repr [| 42 |]) <> Obj.tag (Obj.repr [| 42.0 |])

  let[@cold] nonempty_vec_to_local_float_iarray_slow t ~length ~first_elem = exclave_
    let r = Array.create_local ~len:length first_elem in
    for i = 0 to length - 1 do
      let e = unsafe_get t i in
      Array.unsafe_set r i e
    done;
    unsafe_iarray_of_array__promise_no_mutation r
  ;;

  (* Calls [unsafe_array_sub], which is basically a local allocation and a memcpy.

     ...unless [t] represents an array of floats. In that case, [caml_array_sub_local]
     will preserve the tag of the input array. [float Uniform_array.t] is tagged like an
     array, but [float Iarray.t] is tagged with [Double_array_tag] (unless compiling with
     -no-flat-floatarray).

     So... in that case, we can't use [unsafe_array_sub], and have to write out the for
     loop. *)
  let to_local_iarray t = exclave_
    let length = length t in
    if length = 0
    then unsafe_iarray_of_array__promise_no_mutation [||]
    else (
      let first_elem = unsafe_get t 0 in
      if (not float_arrays_are_flat) && Obj.tag (Obj.repr first_elem) = Obj.double_tag
      then nonempty_vec_to_local_float_iarray_slow t ~length ~first_elem
      else (
        let non_float_array =
          Expert.unsafe_inner t |> Arr_impl.unsafe_to_array_inplace__promise_not_a_float
        in
        unsafe_array_sub non_float_array 0 length))
  ;;

  let to_alist t =
    let result = ref [] in
    for i = max_index t downto 0 do
      result := (i, unsafe_get t i) :: !result
    done;
    !result
  ;;

  (* Convert to a sequence but does not attempt to protect against modification
     in the vec. *)
  let to_sequence_mutable t =
    Sequence.unfold_step ~init:0 ~f:(fun i ->
      if i >= length t then Done else Yield { value = unsafe_get t i; state = i + 1 })
  ;;

  let to_sequence t = to_sequence_mutable (copy t)

  let of_list xs =
    let t = create ~initial_capacity:(List.length xs) () in
    List.iter xs ~f:(push_back t);
    t
  ;;

  let of_array arr = init (Array.length arr) ~f:(fun i -> Array.get arr i)

  let of_sequence seq =
    (* We don't know the length of seq, so we can't set an initial capacity *)
    let t = create () in
    Sequence.iter seq ~f:(push_back t);
    t
  ;;

  [%%template
  [@@@kind.default
    k
    = ( float32
      , bits64
      , value
      , immediate64
      , value & value
      , immediate64 & immediate64
      , value & value & value
      , immediate64 & immediate64 & immediate64
      , value & value & value & value
      , immediate64 & immediate64 & immediate64 & immediate64 )]

  let foldi t ~init ~f =
    let r = ref init in
    for i = 0 to (max_index [@kind k]) t do
      r := f i !r ((unsafe_get [@kind k]) t i)
    done;
    !r
  ;;

  let fold t ~init ~f =
    let r = ref init in
    for i = 0 to (max_index [@kind k]) t do
      r := f !r ((unsafe_get [@kind k]) t i)
    done;
    !r
  ;;

  let foldi_local_accum t ~init:acc ~f = exclave_
    let rec aux t i ~acc ~f = exclave_
      if i >= (length [@kind k]) t
      then acc
      else (
        let acc = f i acc ((unsafe_get [@kind k]) t i) in
        aux t (i + 1) ~acc ~f)
    in
    aux t 0 ~acc ~f
  ;;

  let rec foldi_until' t ~f ~acc ~finish ~max_index i =
    if i > max_index
    then finish acc
    else (
      match (f i acc ((unsafe_get [@kind k]) t i) : _ Continue_or_stop.t) with
      | Stop s -> s
      | Continue acc -> (foldi_until' [@kind k]) t ~f ~max_index (i + 1) ~acc ~finish)
  ;;

  let foldi_until t ~init ~f ~finish =
    (foldi_until' [@kind k]) t ~f ~acc:init ~finish ~max_index:((max_index [@kind k]) t) 0
  ;;]

  include%template Blit.Make1 [@modality portable] (struct
      type nonrec 'a t = 'a t

      let create_like ~len _t =
        (* Note that even though we [unsafe_create_uninitialized], every time this function
           is called, the [Vec] is immediately blitted with valid values. *)
        Kernel.unsafe_create_uninitialized ~len
      ;;

      let length = length
      let unsafe_blit = unsafe_blit
    end)

  [%%template
  [@@@kind.default
    k
    = ( float32
      , bits64
      , immediate64
      , value & value
      , immediate64 & immediate64
      , value & value & value
      , immediate64 & immediate64 & immediate64
      , value & value & value & value
      , immediate64 & immediate64 & immediate64 & immediate64 )]

  (* hand write for lack of a functor *)
  let sub t ~pos ~len =
    (* we don't need this *)
    let (_ : _) = Kernel.unsafe_create_uninitialized [@kind k] in
    Ordered_collection_common.check_pos_len_exn
      ~pos
      ~len
      ~total_length:((length [@kind k]) t);
    (init [@kind k]) len ~f:(fun i -> (unsafe_get [@kind k]) t (pos + i))
  ;;

  let blit (type a : k) ~(src : (a t[@kind k])) ~src_pos ~dst ~dst_pos ~len =
    (* we don't need this *)
    Ordered_collection_common.check_pos_len_exn
      ~pos:src_pos
      ~len
      ~total_length:((length [@kind k]) src);
    Ordered_collection_common.check_pos_len_exn
      ~pos:dst_pos
      ~len
      ~total_length:((length [@kind k]) dst);
    if len > 0 then (unsafe_blit [@kind k]) ~src ~src_pos ~dst ~dst_pos ~len
  ;;]

  [%%template
  [@@@kind.default
    k
    = ( float32
      , bits64
      , value
      , immediate64
      , value & value
      , immediate64 & immediate64
      , value & value & value
      , immediate64 & immediate64 & immediate64
      , value & value & value & value
      , immediate64 & immediate64 & immediate64 & immediate64 )]

  (** Returns the length of the longest prefix for which [f] is true. *)
  let take_while_len (type a : k) (t : (a t[@kind k])) ~(local_ f) : int =
    let rec loop i =
      if i >= (length [@kind k]) t || not (f ((get [@kind k]) t i))
      then i
      else (loop [@tailcall]) (i + 1)
    in
    loop 0 [@nontail]
  ;;

  let take_while t ~f =
    let len = (take_while_len [@kind k]) t ~f in
    (sub [@kind k]) t ~pos:0 ~len
  ;;]

  module Inplace = struct
    [%%template
    [@@@kind.default
      k
      = ( float32
        , bits64
        , value
        , immediate64
        , value & value
        , immediate64 & immediate64
        , value & value & value
        , immediate64 & immediate64 & immediate64
        , value & value & value & value
        , immediate64 & immediate64 & immediate64 & immediate64 )]

    let sub t ~pos ~len =
      Ordered_collection_common.check_pos_len_exn
        ~pos
        ~len
        ~total_length:((length [@kind k]) t);
      if pos <> 0 then (blit [@kind k]) ~src:t ~src_pos:pos ~dst:t ~dst_pos:0 ~len;
      (shrink_to [@kind k]) t ~len
    ;;

    let take_while t ~f =
      let to_len = (take_while_len [@kind k]) t ~f in
      (shrink_to [@kind k]) t ~len:to_len
    ;;

    let filter t ~f =
      let dest = ref 0 in
      for i = 0 to (max_index [@kind k]) t do
        let x = (unsafe_get [@kind k]) t i in
        if f x
        then (
          if !dest < i then (unsafe_set [@kind k]) t !dest x;
          incr dest)
      done;
      let dest = !dest in
      (shrink_to [@kind k]) t ~len:dest
    ;;

    let map t ~f =
      for i = 0 to (max_index [@kind k]) t do
        (unsafe_set [@kind k]) t i (f ((unsafe_get [@kind k]) t i))
      done
    ;;

    let mapi t ~f =
      for i = 0 to (max_index [@kind k]) t do
        (unsafe_set [@kind k]) t i (f i ((unsafe_get [@kind k]) t i))
      done
    ;;]
  end

  [%%template
  [@@@kind.default
    k
    = ( float32
      , bits64
      , value
      , immediate64
      , value & value
      , immediate64 & immediate64
      , value & value & value
      , immediate64 & immediate64 & immediate64
      , value & value & value & value
      , immediate64 & immediate64 & immediate64 & immediate64 )]

  let rec forall2__same_length (t1 @ m) (t2 @ m) ~f i length =
    if i >= length
    then true
    else
      f ((unsafe_get [@mode m] [@kind k]) t1 i) ((unsafe_get [@mode m] [@kind k]) t2 i)
      && (forall2__same_length [@mode m] [@kind k]) t1 t2 ~f (i + 1) length
  [@@mode m = (local, global)]
  ;;

  let equal equal (t @ m) (t' @ m) =
    let length' = (length [@kind k]) t in
    if length' <> (length [@kind k]) t'
    then false
    else (forall2__same_length [@mode m] [@kind k]) t t' ~f:equal 0 length' [@nontail]
  [@@mode m = (local, global)]
  ;;

  let clear (type a : k) (t : (a t[@kind k])) =
    if (length [@kind k]) t > 0 then (shrink_to [@kind k]) t ~len:0
  ;;]

  let clear_imm (t : 'a t) = if length t > 0 then shrink_to_imm t ~len:0

  [%%template
  [@@@kind.default
    k
    = ( float32
      , bits64
      , value
      , immediate64
      , value & value
      , immediate64 & immediate64
      , value & value & value
      , immediate64 & immediate64 & immediate64
      , value & value & value & value
      , immediate64 & immediate64 & immediate64 & immediate64 )]

  let sexp_of_t (type a : k) (sexp_of_a : a -> Sexp.t) t =
    Array.init ((length [@kind k]) t) ~f:(fun i -> sexp_of_a ((unsafe_get [@kind k]) t i))
    |> [%sexp_of: Sexp.t array]
  ;;

  let is_empty t = (length [@kind k]) t = 0

  let exists t ~f =
    let i = ref 0 in
    let n = (length [@kind k]) t in
    let result = ref false in
    while !i < n && not !result do
      if f ((unsafe_get [@kind k]) t !i) then result := true else incr i
    done;
    !result
  ;;

  let for_all t ~f =
    let i = ref 0 in
    let n = (length [@kind k]) t in
    let result = ref true in
    while !i < n && !result do
      if f ((unsafe_get [@kind k]) t !i) then incr i else result := false
    done;
    !result
  ;;

  let mem t a ~equal = (exists [@kind k] [@inlined hint]) t ~f:(equal a) [@nontail]]

  let count t ~f = Container.count ~fold t ~f
  let sum module_ t ~f = Container.sum ~fold module_ t ~f

  (* Reimplemented for layouts *)

  [%%template
  [@@@kind.default
    k
    = ( float32
      , bits64
      , immediate64
      , value & value
      , immediate64 & immediate64
      , value & value & value
      , immediate64 & immediate64 & immediate64
      , value & value & value & value
      , immediate64 & immediate64 & immediate64 & immediate64 )]

  let count t ~f =
    (fold [@kind k]) t ~init:0 ~f:(fun n a -> if f a then n + 1 else n) [@nontail]
  ;;

  let sum (type a) (module M : Container.Summable with type t = a) t ~f =
    (fold [@kind k]) t ~init:M.zero ~f:(fun n a -> M.( + ) n (f a)) [@nontail]
  ;;]

  (* The code for [find] and [find_exn] would be simpler (wouldn't involve threading
     through [max_index]) if we iterated backward, but we iterate forward to be consistent
     with other containers. *)

  let rec find' t ~f ~max_index i =
    if i > max_index
    then None
    else (
      let x = unsafe_get t i in
      if f x then Some x else find' t ~f ~max_index (i + 1))
  ;;

  let[@cold] raise__not_found () =
    raise (Base.Not_found_s [%message "Vec.find_exn: not found"])
  ;;

  (* Tailcalls to raising functions are to be avoided, as the stack traces are much worse.
     Instead, we try really hard to inline wrapper functions that just perform non-tail
     calls to the raising functions.
  *)
  let[@inline always] raise__not_found () = raise__not_found () [@nontail]

  [%%template
  [@@@kind.default
    k
    = ( float32
      , bits64
      , value
      , immediate64
      , value & value
      , immediate64 & immediate64
      , value & value & value
      , immediate64 & immediate64 & immediate64
      , value & value & value & value
      , immediate64 & immediate64 & immediate64 & immediate64 )]

  let rec find_exn' t ~f ~max_index i =
    if i > max_index
    then (
      match raise__not_found () with
      | (_ : Nothing.t) -> .)
    else (
      let x = (unsafe_get [@kind k]) t i in
      if f x then x else (find_exn' [@kind k]) t ~f ~max_index (i + 1))
  ;;

  let find_exn t ~f = (find_exn' [@kind k]) t ~f ~max_index:((max_index [@kind k]) t) 0]

  let find t ~f = find' t ~f ~max_index:(max_index t) 0

  let rec findi' t ~f ~max_index i =
    if i > max_index
    then None
    else (
      let x = unsafe_get t i in
      if f x then Some (i, x) else findi' t ~f ~max_index (i + 1))
  ;;

  let findi t ~f = findi' t ~f ~max_index:(max_index t) 0

  let find_and_remove t ~f =
    match findi t ~f with
    | None -> None
    | Some (i, found) ->
      remove_exn t i;
      Some found
  ;;

  let rec find_map' t ~f ~max_index i =
    if i > max_index
    then None
    else (
      match f (unsafe_get t i) with
      | None -> find_map' t ~f ~max_index (i + 1)
      | some -> some)
  ;;

  let find_map t ~f = find_map' t ~f ~max_index:(max_index t) 0

  let rec fold_result' t ~f ~acc ~max_index i =
    if i > max_index
    then Ok acc
    else (
      match f acc (unsafe_get t i) with
      | Ok acc -> fold_result' t ~f ~max_index (i + 1) ~acc
      | err -> err)
  ;;

  let fold_result t ~init ~f = fold_result' t ~f ~acc:init ~max_index:(max_index t) 0

  let rec fold_until' t ~f ~acc ~finish ~max_index i =
    if i > max_index
    then finish acc
    else (
      match (f acc (unsafe_get t i) : _ Continue_or_stop.t) with
      | Stop s -> s
      | Continue acc -> fold_until' t ~f ~max_index (i + 1) ~acc ~finish)
  ;;

  let fold_until t ~init ~f ~finish =
    fold_until' t ~f ~acc:init ~finish ~max_index:(max_index t) 0
  ;;

  let max_elt t ~compare =
    if is_empty t
    then None
    else (
      let max = ref (unsafe_get t 0) in
      for i = 1 to max_index t do
        let x = unsafe_get t i in
        let max' = !max in
        max := if compare max' x < 0 then x else max'
      done;
      Some !max)
  ;;

  let min_elt t ~compare =
    if is_empty t
    then None
    else (
      let min = ref (unsafe_get t 0) in
      for i = 1 to max_index t do
        let x = unsafe_get t i in
        let min' = !min in
        min := if compare min' x > 0 then x else min'
      done;
      Some !min)
  ;;

  let[@inline available] to_array t = Array.init (length t) ~f:(unsafe_get t)

  [%%template
  [@@@kind.default k = (float32, bits64)]

  module [@kind] Arr = Arr_impl [@kind k]

  let to_array t = Arr.init ((length [@kind k]) t) ~f:((unsafe_get [@kind k]) t)]

  [%%template
  [@@@kind.default
    k
    = ( float32
      , bits64
      , value
      , immediate64
      , value & value
      , immediate64 & immediate64
      , value & value & value
      , immediate64 & immediate64 & immediate64
      , value & value & value & value
      , immediate64 & immediate64 & immediate64 & immediate64 )]

  let t_of_sexp a_of_sexp t =
    let arr = [%of_sexp: Sexp.t array] t in
    (init [@kind k]) (Array.length arr) ~f:(fun i -> Array.unsafe_get arr i |> a_of_sexp)
  ;;

  let compare cmp (t1 @ m) (t2 @ m) =
    let len1 = (length [@kind k]) t1 in
    let len2 = (length [@kind k]) t2 in
    let min_len = Int.min len1 len2 in
    let result = ref 0 in
    let i = ref 0 in
    while !i < min_len && !result = 0 do
      result
      := cmp
           ((unsafe_get [@mode m] [@kind k]) t1 !i)
           ((unsafe_get [@mode m] [@kind k]) t2 !i);
      i := !i + 1
    done;
    if !result = 0 then Int.compare len1 len2 else !result
  [@@mode m = (local, global)]
  ;;

  let unsafe_swap t i j =
    let e = (unsafe_get [@kind k]) t i in
    (unsafe_set [@kind k]) t i ((unsafe_get [@kind k]) t j);
    (unsafe_set [@kind k]) t j e
  ;;

  let swap t i j =
    (check_index [@kind k]) t i ~op:"swap";
    (check_index [@kind k]) t j ~op:"swap";
    (unsafe_swap [@kind k]) t i j
  ;;

  let swap_to_last_and_pop t i =
    (check_index [@kind k]) t i ~op:"swap_to_last_and_pop";
    (unsafe_swap [@kind k]) t i ((max_index [@kind k]) t);
    (pop_back_exn [@kind k]) t
  ;;]

  let to_iarray t =
    (to_array [@inlined hint]) t |> unsafe_iarray_of_array__promise_no_mutation
  ;;

  let swap_to_last_and_pop_imm t i =
    check_index t i ~op:"swap_to_last_and_pop";
    unsafe_swap t i (max_index t);
    pop_back_imm_exn t
  ;;

  module Stable = struct
    module V1 = struct
      type nonrec 'a t = 'a t [@@deriving compare ~localize, sexp]

      include%template Bin_prot.Utils.Make_iterable_binable1 [@modality portable] (struct
          type nonrec 'a t = 'a t
          type 'a el = 'a [@@deriving bin_io]

          let caller_identity =
            Bin_prot.Shape.Uuid.of_string "2ec1d047-7cf8-49bc-991b-0badd17d8359"
          ;;

          let module_name = Some "Vec"
          let init ~len ~next = init len ~f:(fun _ -> next ()) [@nontail]
          let iter = iter
          let length = length
        end)

      (* [Make_iterable_binable] doesn't provide a stable witness, but is stable. *)
      let stable_witness (_ : 'a Stable_witness.t) = Stable_witness.assert_stable
    end
  end

  module For_testing = struct
    let%template zero_unused_capacity t =
      let inner : _ I64.Array.t = (Expert.unsafe_inner [@kind bits64]) t in
      let inner : I64.t I64.Array.t = Obj.magic inner in
      let capacity = (capacity [@kind bits64]) t in
      let length = (length [@kind bits64]) t in
      for i = length to capacity - 1 do
        I64.Array.set inner i #0L
      done
    ;;
  end

  module Expert = struct
    let[@inline] unsafe_inner t = Arr_impl.unwrap (Expert.unsafe_inner t)
  end
end

include With_integer_index

module type S = Vec_intf.S

module%template.portable Make (M : Intable.S) = struct
  include With_integer_index

  let[@inline always] [@zero_alloc] to_int_exn index =
    (M.to_int_exn [@zero_alloc assume]) index
  ;;

  let[@inline always] [@zero_alloc] of_int_exn index =
    (M.of_int_exn [@zero_alloc assume]) index
  ;;

  [%%template
  [@@@kind.default
    k
    = ( float32
      , bits64
      , value
      , immediate64
      , value & value
      , immediate64 & immediate64
      , value & value & value
      , immediate64 & immediate64 & immediate64
      , value & value & value & value
      , immediate64 & immediate64 & immediate64 & immediate64 )]

  let[@inline always] unsafe_get t index = (unsafe_get [@kind k]) t (to_int_exn index)
  let get t index = (get [@kind k]) t (to_int_exn index)]

  let maybe_get t index = maybe_get t (to_int_exn index)
  let maybe_get_local t index = exclave_ maybe_get_local t (to_int_exn index)
  let maybe_get_or_null t index = maybe_get_or_null t (to_int_exn index)

  let[@inline always] unsafe_set_imm t index x : unit =
    unsafe_set_imm t (to_int_exn index) x
  ;;

  let set_imm t index x : unit = set_imm t (to_int_exn index) x

  [%%template
  [@@@kind.default
    k
    = ( float32
      , bits64
      , value
      , immediate64
      , value & value
      , immediate64 & immediate64
      , value & value & value
      , immediate64 & immediate64 & immediate64
      , value & value & value & value
      , immediate64 & immediate64 & immediate64 & immediate64 )]

  let[@inline always] unsafe_set t index x : unit =
    (unsafe_set [@kind k]) t (to_int_exn index) x
  ;;

  let set t index x : unit = (set [@kind k]) t (to_int_exn index) x
  let next_free_index t = (next_free_index [@kind k]) t |> of_int_exn

  let foldi t ~init ~f =
    (foldi [@kind k] [@inlined hint]) t ~init ~f:(fun [@inline] int accum x ->
      f (of_int_exn int) accum x)
    [@nontail]
  ;;

  let foldi_local_accum t ~init ~f = exclave_
    (foldi_local_accum [@kind k] [@inlined hint])
      t
      ~init
      ~f:(fun [@inline] int accum x -> exclave_ f (of_int_exn int) accum x)
    [@nontail]
  ;;

  let foldi_until t ~init ~f ~finish =
    (foldi_until [@kind k] [@inlined hint])
      t
      ~init
      ~f:(fun [@inline] int accum x -> f (of_int_exn int) accum x)
      ~finish [@nontail]
  ;;

  let iteri t ~f =
    (iteri [@kind k] [@inlined hint]) t ~f:(fun [@inline] int x -> f (of_int_exn int) x)
    [@nontail]
  ;;

  let push_back_index t element = (push_back_index [@kind k]) t element |> of_int_exn]

  let push_back_index_imm t e = push_back_index_imm t e |> of_int_exn

  let findi t ~f =
    match (findi [@inlined hint]) t ~f with
    | Some (i, a) -> Some (of_int_exn i, a)
    | None -> None
  ;;

  let to_alist t =
    (* We could do:
       {[
         to_alist t |> List.map ~f:(fun (i, x) -> of_int_exn i, x)
       ]}

       at the expense of an extra allocation. This is a bit more copy-pasty,
       but avoids that.
    *)
    let result = ref [] in
    for i = max_index t downto 0 do
      let m = of_int_exn i in
      result := (m, unsafe_get t m) :: !result
    done;
    !result
  ;;

  [%%template
  [@@@kind.default
    k
    = ( float32
      , bits64
      , value
      , immediate64
      , value & value
      , immediate64 & immediate64
      , value & value & value
      , immediate64 & immediate64 & immediate64
      , value & value & value & value
      , immediate64 & immediate64 & immediate64 & immediate64 )]

  let grow_to_include t idx ~default =
    (grow_to_include [@kind k]) t (to_int_exn idx) ~default
  ;;

  let grow_to' t ~len ~default =
    (grow_to' [@kind k]) t ~len ~default:(fun [@inline] idx -> default (of_int_exn idx))
  ;;

  let grow_to_include' t idx ~default =
    (grow_to_include' [@kind k]) t (to_int_exn idx) ~default:(fun [@inline] idx ->
      default (of_int_exn idx))
  ;;]

  module Inplace = struct
    include Inplace

    [%%template
    [@@@kind.default
      k
      = ( float32
        , bits64
        , value
        , immediate64
        , value & value
        , immediate64 & immediate64
        , value & value & value
        , immediate64 & immediate64 & immediate64
        , value & value & value & value
        , immediate64 & immediate64 & immediate64 & immediate64 )]

    let sub t ~pos ~len = (sub [@kind k]) t ~pos:(to_int_exn pos) ~len

    let mapi t ~f =
      (mapi [@kind k]) t ~f:(fun [@inline] int x -> f (of_int_exn int) x) [@nontail]
    ;;]
  end

  [%%template
  [@@@kind.default
    k
    = ( float32
      , bits64
      , value
      , immediate64
      , value & value
      , immediate64 & immediate64
      , value & value & value
      , immediate64 & immediate64 & immediate64
      , value & value & value & value
      , immediate64 & immediate64 & immediate64 & immediate64 )]

  let swap t index1 index2 = (swap [@kind k]) t (to_int_exn index1) (to_int_exn index2)
  let swap_to_last_and_pop t index = (swap_to_last_and_pop [@kind k]) t (to_int_exn index)]

  let swap_to_last_and_pop_imm t index = swap_to_last_and_pop_imm t (to_int_exn index)
end
[@@inline]
