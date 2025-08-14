type stlcT =
  (* 基本の型 *)
  | Int
  (* 関数型 stlcT -> stlcT *)
  | FunT of stlcT * stlcT
  (* 型変数 αi = TVar i *)
  | TVar of int

(* 単一化アルゴリズム *)
(* 型変数S (tvar) がTに含まれるかどうかを判定する *)
let rec is_contain (tvar : stlcT) (t : stlcT) : bool =
  match t with
  | Int -> false
  | FunT (t1, t2) -> is_contain tvar t1 || is_contain tvar t2
  | TVar i -> tvar = TVar i

(* 代入リスト全体を、単一の型に適用する関数 *)
let rec apply_subset (subset : (int * stlcT) list) (t : stlcT) : stlcT =
  match t with
  | Int -> Int
  | FunT (t1, t2) -> FunT (apply_subset subset t1, apply_subset subset t2)
  | TVar i -> (
      match List.assoc_opt i subset with
      (* 代入が見つかった場合、その結果に対しても再帰的に適用することで
          α1:=α2, α2:=Int のような連鎖した代入を解決し、最終的な Int を得る *)
      | Some applied_t -> apply_subset subset applied_t
      | None -> t)

(* 既存の制約リスト remain に対して、新しい代入 new_tvar を適用する *)
let apply_tvar_remain (new_tvar : (int * stlcT) list)
    (remain : (stlcT * stlcT) list) : (stlcT * stlcT) list =
  List.map
    (fun (t1, t2) -> (apply_subset new_tvar t1, apply_subset new_tvar t2))
    remain

(* 既存の代入リスト subset の右辺に対して、新しい代入 new_tvar を適用する *)
let apply_tvar_to_subset (new_tvar : (int * stlcT) list)
    (subset : (int * stlcT) list) : (int * stlcT) list =
  List.map (fun (v, t) -> (v, apply_subset new_tvar t)) subset

(* 新しい代入 new_tvar を既存の代入リスト subset に追加 (正しくは合成) する *)
let append_tvar_to_subset (new_tvar : (int * stlcT) list)
    (subset : (int * stlcT) list) : (int * stlcT) list =
  new_tvar @ apply_tvar_to_subset new_tvar subset

let rec unify_helper (e : (stlcT * stlcT) list) (subset : (int * stlcT) list) :
    ((int * stlcT) list, string) result =
  match e with
  (* (1) E = {} のとき、「subset という解あり」を答として返す。 *)
  (* E = [] -> Ok subset *)
  | [] -> Ok subset
  (* (2) E̸ = fg のとき、E から任意の等式 1 つを選び S = T とする。*)
  (* (s, t) :: remain -> some process *)
  | (s, t) :: remain -> (
      if s = t then
        (* (2-1) S = T の時、つまり、もともと S と T が同一の型の時、unify_helper(E - {S = T}; Θ) を呼び出して、その答を返す。 *)
        unify_helper remain subset
      else
        match (s, t) with
        (* (2-2) S ≠ T で、S が型変数のとき、 *)
        | TVar i, t ->
            let t = apply_subset subset t in
            if is_contain (TVar i) t then
              (* (2-2-1) 型 T に S が現れるなら、「解なし」を答として返す。 *)
              Error "Unification failed..."
            else
              (* (2-2-2) 型 T に S が現れないなら、S := T を新しい subset とし、E − {S = T} に S := T を適用したものを新しい E として、最初に戻る。 *)
              (* 既存の代入 subset と新しい代入 S := T を合成して、新しい subset を作る *)
              let new_tvar = [ (i, t) ] in
              (* 残りの制約と、既存の代入の両方を、新しい代入 new_tvar で更新する *)
              let new_remain = apply_tvar_remain new_tvar remain in
              let new_subset = append_tvar_to_subset new_tvar subset in
              unify_helper new_remain new_subset
        (* (2-3) S ≠ T で、T が型変数のとき、S と T を逆にして 1 つ前のケースを適用 *)
        | t, TVar i -> unify_helper ((TVar i, t) :: remain) subset
        (* (2-4) (2-5) S ≠ T で、S = S1 -> S2, T = T1 -> T2 のとき、E = (E − {S = T}) ∪ {S1 = T1; S2 = T2}を新しい E として、最初に戻る。 *)
        | FunT (s1, s2), FunT (t1, t2) ->
            unify_helper ((s1, t1) :: (s2, t2) :: remain) subset
        (* 上記のいずれのケースでもないとき、「解なし」を答として返す。 *)
        | _ -> Error "Unification failed...")

let unify (e : (stlcT * stlcT) list) = unify_helper e []

(* --- 実行テスト --- *)
(* stlcT型の値をstringに変換する *)
let rec string_of_stlcT = function
  | Int -> "Int"
  | FunT (t1, t2) ->
      "(" ^ string_of_stlcT t1 ^ " -> " ^ string_of_stlcT t2 ^ ")"
  | TVar i -> "α" ^ string_of_int i

(* 単一化適用後の結果を表示する *)
let show_result (input : (stlcT * stlcT) list) : unit =
  let test_result = unify input in
  match test_result with
  | Ok subset ->
      print_endline "Unification successful!";
      let sorted_subset = List.sort (fun (a, _) (b, _) -> compare a b) subset in
      List.iter
        (fun (i, t) ->
          print_endline (string_of_stlcT (TVar i) ^ " := " ^ string_of_stlcT t))
        sorted_subset
  | Error msg -> print_endline msg

(* 単一化のテスト *)
(* 対応リスト
  (a, b) : a = b,
  Int : int,
  FunT (a, b) : a -> b,
  TVar i : αi (eg. TVar 1 : α1)
*)

(* 以下の入力例の意味 α1 -> int = α2 -> α1 *)
let input = [ (FunT (TVar 1, Int), FunT (TVar 2, TVar 1)) ];;

show_result input

(* 以下の入力例の意味 α1 -> int = (α1 -> int) -> α1 *)
let input2 = [ (FunT (TVar 1, Int), FunT (FunT (TVar 1, Int), TVar 1)) ];;

show_result input2
