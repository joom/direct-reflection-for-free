tm : Type
ty : Type
string : Type

tyunit : ty
tystring : ty
arr : ty -> ty -> ty
sum : ty -> ty -> ty
pair : ty -> ty -> ty
mu : (ty -> ty) -> ty
				   
app : tm -> tm -> tm
lam : ty -> (tm -> tm) -> tm

mkunit : tm
strlit : string -> tm

inl : tm -> tm
inr : tm -> tm
case : tm -> tm -> tm -> tm

mkpair : tm -> tm -> tm
fst : tm -> tm
snd : tm -> tm

fold : tm -> tm
unfold : tm -> tm
