# Direct Reflection for Free!

Documents (TeX, slides etc.) for the work on using `Data` and `Typeable` to get a direct reflection system for free, when we're implementing a toy language in Haskell.

Submitted for the ICFP 2019 Student Research Competition, got 3rd prize in the graduate category. [[pdf]](http://www.cs.princeton.edu/~ckorkut/papers/icfp-src-19-reflection.pdf)

This repo still contains a lot of broken code, it will eventually get straightened out, I'm still working on a full paper.

## Abstract

Haskell is a popular language for language implementations. However, adding metaprogramming features to a language implemented in Haskell requires a significant amount of boilerplate code. Using Data and Typeable style of generic programming in Haskell, we describe a design pattern that allows automatic derivation of metaprogramming features from your language implementation. If you have evaluation, you can evaluate quasiquoted terms for free. If you have type-checking, you can type-check quasiquoted terms for free. If you have a parser, you can have parser reflection for free. This design pattern is applicable to both untyped and typed languages, and can implement various features of metaprogramming.

## Acknowledgments

I'd like to thank Matt Chan and Gabriel Gonzalez for inspiring the idea of a bridge between Haskell and another language.
