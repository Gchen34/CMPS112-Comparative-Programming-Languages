(* $Id: bigint.ml,v 1.5 2014-11-11 15:06:24-08 - - $ *)
(* Assignment 2*)
(*Guangyang Chen gchen34@ucsc.edu*)
(*Justin Clark judclark@ucsc.edu*)

open Printf

module Bigint = struct

    type sign     = Pos | Neg
    type bigint   = Bigint of sign * int list
    let  radix    = 10
    let  radixlen =  1

    let car       = List.hd
    let cdr       = List.tl
    let map       = List.map
    let reverse   = List.rev
    let strcat    = String.concat
    let strlen    = String.length
    let strsub    = String.sub
    let zero      = Bigint (Pos, [])

    let charlist_of_string str = 
        let last = strlen str - 1
        in  let rec charlist pos result =
            if pos < 0
            then result
            else charlist (pos - 1) (str.[pos] :: result)
        in  charlist last []

    let bigint_of_string str =
        let len = strlen str
        in  let to_intlist first =
                let substr = strsub str first (len - first) in
                let digit char = int_of_char char - int_of_char '0' in
                map digit (reverse (charlist_of_string substr))
            in  if   len = 0
                then zero
                else if   str.[0] = '_'
                     then Bigint (Neg, to_intlist 1)
                     else Bigint (Pos, to_intlist 0)

    let string_of_bigint (Bigint (sign, value)) =
        match value with
        | []    -> "0"
        | value -> let reversed = reverse value
                   in strcat ""
                       ((if sign = Pos then "" else "-") ::
                         (map string_of_int reversed))
    
    let clear_zero ls = 
        let rec clear_ l = 
            match (l) with
            | []  -> []
            | [0] -> []
            | car::cdr -> 
                let cdr' = clear_ cdr in 
                    match (car, cdr') with 
                    | 0, [] -> []
                    | _ -> car :: cdr'
        in clear_ ls

    let rec cmp' list1 list2 = match (list1, list2) with
        | [], []                 ->  0
        | list1, []              ->  1
        | [], list2              -> -1
        | car1::cdr1, car2::cdr2 -> 
            let cmp = cmp' cdr1 cdr2 in 
            if cmp = 0 && car1 != car2 then 
            (if car1 > car2 then 1 else 
            (if car1 < car2 then -1 else 0))
            else cmp
            
    let add' list1 list2 =
        let rec add'' list1 list2 carry =  
            match (list1, list2, carry) with
            | list1, [], 0       -> list1
            | [], list2, 0       -> list2
            | list1, [], carry   -> add'' list1 [carry] 0
            | [], list2, carry   -> add'' [carry] list2 0
            | car1::cdr1, car2::cdr2, carry ->
                let sum = car1 + car2 + carry
                in  sum mod radix :: add'' cdr1 cdr2 (sum / radix)
        in add'' list1 list2 0

    let sub' list1 list2 = 
        let rec sub'' list1 list2 carry = 
            match (list1, list2, carry) with
        | list1, [], 0      -> list1
        | [], list2, 0      -> list2
        | list1, [], carry  -> sub'' list1 [carry] 0
        | [], list2, carry  -> sub'' [carry] list2 0
        | car1::cdr1, car2::cdr2, carry -> 
            let diff = car1 - car2 - carry
            in (diff + radix) mod radix :: sub'' cdr1 cdr2 
            (if diff < 0 then 1 else 0)
        in clear_zero (sub'' list1 list2 0)

    let add (Bigint (neg1, value1)) (Bigint (neg2, value2)) =
        match (neg1, neg2) with
            | Pos, Neg  -> if (cmp' value1 value2) = 1
                then Bigint (Pos, sub' value1 value2) 
                else Bigint (Neg, sub' value2 value1)
            | Neg, Pos  -> if (cmp' value1 value2) = 1
                then Bigint (Neg, sub' value1 value2)
                else Bigint (Pos, sub' value2 value1)
            | _         -> Bigint (neg1, add' value1 value2)

    
    let sub (Bigint (neg1, value1)) (Bigint (neg2, value2)) =
        match (neg1, neg2) with 
        | Pos, Neg  -> Bigint (Pos, add' value1 value2) 
        | Neg, Pos  -> Bigint (Neg, add' value1 value2)
        | Pos, Pos  -> if (cmp' value1 value2) = 1 
        then Bigint (Pos, sub' value1 value2) 
        else Bigint (Neg, sub' value2 value1)
        | Neg, Neg  -> if (cmp' value1 value2) = 1 
        then Bigint (Neg, sub' value1 value2) 
        else Bigint (Pos, sub' value2 value1)
    
    let rec mulval' ls value carry =
        match (ls, value, carry) with
        | ls, 0, 0              -> [0]
        | [], value, 0          -> []
        | ls, 0, carry          -> [carry]
        | [], value, carry      -> [carry]
        | car::cdr, value, carry ->
            let product = car * value + carry
            in product mod radix :: mulval' cdr value (product / radix)
    
    let rec shift_right ls times = if times = 0 
        then ls else shift_right (0 :: ls) (times - 1)

    let rec mul' list1 list2 =
        let rec mul'' list1 list2 carry digit =
            match (list1, list2, carry) with
            | list1, [], []      -> list1
            | [], list2, []      -> list2
            | list1, [], carry   -> carry
            | [], list2, carry   -> carry
            | list1, car::cdr, [] ->
                mul'' list1 cdr (mulval' list1 car 0) (digit + 1)
            | list1, car::cdr, carry ->
                let product = mulval' list1 car 0
                in mul'' list1 cdr 
                (add' (shift_right product digit) carry) (digit + 1)
        in mul'' list1 list2 [] 0
            
    let mul (Bigint (neg1, value1)) (Bigint (neg2, value2)) =
       if neg1 = neg2 
       then Bigint(Pos, mul' value1 value2) 
       else Bigint(Neg, mul' value1 value2)

    let divrem dividend dividor = 
        let rec egydivrem dividend quotient accum =
            if (cmp' (sub' dividend accum) accum) = -1
            then quotient, accum
            else
                let quotient', accum' = egydivrem 
                dividend (add' quotient quotient) 
                (add' accum accum) in
                let sum = add' accum accum' in
                if (cmp' sum dividend) = 1 then quotient', accum'
                else (add' quotient' quotient), sum
        in let quotient, approx = egydivrem dividend [1] dividor
        in 
        quotient, sub' dividend approx

    let div (Bigint (neg1, value1)) (Bigint (neg2, value2)) =
       if neg1 = neg2 
       then Bigint(Pos, let quot, rem = divrem value1 value2 in quot) 
       else Bigint(Neg, let quot, rem = divrem value1 value2 in quot)

    let rem (Bigint (neg1, value1)) (Bigint (neg2, value2)) =
       if neg1 = neg2 
       then Bigint(Pos, let quot, rem = divrem value1 value2 in rem) 
       else Bigint(Neg, let quot, rem = divrem value1 value2 in rem)
        
    let rec pow' list1 list2 inclist1 =
      let declist2 = (clear_zero (sub' list2 [1])) in
        if declist2 = [] then list1 else 
        pow' (mul' list1 inclist1) declist2 inclist1    

    let pow (Bigint (neg1, val1)) (Bigint (neg2, val2)) =
      if neg2 = Neg then zero else 
      match (val1, val2) with
      | [], val2   -> zero
      | val1, []   -> Bigint(Pos, [1])
      | val1, val2 -> Bigint(neg1, pow' val1 val2 val1)

end
