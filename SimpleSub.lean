inductive Typ : Type
| Typ_base : Typ
| Type_abs : Typ -> Typ -> Typ
| Typ_array : Typ -> Typ
| Typ_lett : Typ -> Typ
| Typ_sub : Typ -> Typ

inductive Expr : Type
| Var : Expr -> Expr
| Const : Int -> Expr
| Abs : Expr -> Expr -> Expr
| Appl : Expr -> Expr -> Expr
| Rcd : Expr -> Expr
| Proj : Expr -> Expr
| Lett : Expr -> Expr
| Sub : Expr -> Expr

namespace Expr
notation t1 "->" t2 => Typ.typ_abs t1 t2
notation "€" i => Var i
notation "$" x => Const x
notation "λ " T "," t => Abs T t
notation t1 " @ " t2 => Appl t1 t2

open Typ
open Expr

inductive Typing : context → Trm → Typ → Prop
| t_var (Γ : context) (x : ℕ) (T : Typ) : (valid_ctx Γ) → (binds x T Γ) → (typing Γ ($ x) T)
| t_abs (L : Finset ℕ) (Γ : context) (t : Expr) (T1 T2 : Typ) :
        ((x : ℕ) → x ∉ L → (typing ((x, T1) :: Γ) (open₀ t ($ x)) T2)) → (typing Γ (abs T1 t) (typ_abs T1 T2))
| t_app (Γ : context) (t₁ t₂ : Expr) (T1 T2 : Typ) :
        (typing Γ t₁ (typ_abs T1 T2)) → (typing Γ t₂ T1) → typing Γ (app t₁ t₂) T2
| t_rcd
| t_proj
| t_lett
| t_sub
