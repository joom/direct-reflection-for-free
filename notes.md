* Is "Direct Reflection for Free!" a misleading title? Kathrin thinks it is because "for free" is often used for concepts related to parametricity.

I think it's not so misleading because there are "for free" papers that are *not* related to parametricity.
"Dijkstra monads for free" is an example.

* Is here any work on converting host language terms into an encoding back and forth?
This is the only one I know: https://jozefg.bitbucket.io/posts/2014-03-06-church.html
And it's not even about encoding it in an *object* language, it's for encoding it in Haskell itself.

* tight retract?

We want more than a tight retract, actually.

Class bridge (A : Type) :=
  { reify_ty : closed_ty
  ; reify_exp : A -> closed_exp reify_ty
  ; reifies_to_value : forall (a : A) -> is_value (reify_exp a)
  ; reflect_exp : forall (e : closed_exp reify_ty), is_value e -> A
  ; round_trip : forall (a : A), reflect_exp (reify_exp a) (reifies_to_value a) = a
  }.


* read David's dissertation again:
page 19. direct reflection

```
Barzilay identifies a number of downsides of indirect reflection:
- implementing a complex system, like a type checker, is a great deal of work
- ensuring a perfect correspondence between the reflected portions of the implementation and the original implementation is a major task
- the size of a term’s representation will typically grow exponentially with each level of quotation that is applied
```

page 144. there is a good quote about why we reflect the core language and not the surface language.
"Unlike TT, high-level Idris, even in its desugared form, is a quite complicated language that changes on a regular basis. Maintaining an Idris mirror of the data type would add significantly to the maintenance burden."


* look into gradual types, session types, refinement types, linear/modal stuff
  one could write a metaprogram to annotate gradual programs with types
  in general, annotation-like metaprograms could be a good idea to look into
