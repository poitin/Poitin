module Prove where

import Term
import Data.List
import Debug.Trace

prove t = prove' (free t) [] [] t

prove' fv cs fs (Free x) = False
prove' fv cs fs (Bound i) = False
prove' fv cs fs (Lambda x t) = let x' = rename fv x
                               in  prove' (x':fv) cs fs (concrete x' t)
prove' fv cs fs (Con c ts) = c == "True"
prove' fv cs fs (Apply t u) = prove' fv cs fs t && prove' fv cs fs u
prove' fv cs fs (Call f ts) = case lookup f fs of
                                 Just xs -> not (null (intersect xs cs))
prove' fv cs fs (Case t bs) = let cs' = case t of
                                           Free x -> x:cs
                                           _ -> cs
                              in all (\(c,xs,t) -> let fv' = foldr (\x fv -> let x' = rename fv x in x':fv) fv xs
                                                       xs' = take (length xs) fv'
                                                   in  prove' fv' cs' fs (foldr concrete t xs')) bs
prove' fv cs fs (Let x t u) = let x' = rename fv x
                              in  prove' fv cs fs t && prove' (x':fv) cs fs (concrete x' u )
prove' fv cs fs (Letrec f xs t ts) = let fv' = foldr (\x fv -> let x' = rename fv x in x':fv) fv xs
                                         xs' = take (length xs) fv'
                                         f' = rename (fst (unzip fs)) f
                                         t' = renameFun f f' (foldr concrete t xs')
                                     in  prove' fv' cs ((f',xs'):fs) t'



