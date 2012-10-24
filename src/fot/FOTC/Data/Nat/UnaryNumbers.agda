------------------------------------------------------------------------------
-- Unary naturales numbers terms
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Data.Nat.UnaryNumbers where

open import FOTC.Base

------------------------------------------------------------------------------

one    = succ₁ zero
two    = succ₁ one
three  = succ₁ two
four   = succ₁ three
five   = succ₁ four
six    = succ₁ five
seven  = succ₁ six
eight  = succ₁ seven
nine   = succ₁ eight
ten    = succ₁ nine

{-# ATP definition one two three four five six seven eight nine ten #-}

eleven    = succ₁ ten
twelve    = succ₁ eleven
thirteen  = succ₁ twelve
fourteen  = succ₁ thirteen
fifteen   = succ₁ fourteen
sixteen   = succ₁ fifteen
seventeen = succ₁ sixteen
eighteen  = succ₁ seventeen
nineteen  = succ₁ eighteen
twenty    = succ₁ nineteen

{-# ATP definition eleven twelve thirteen fourteen fifteen
                   sixteen seventeen eighteen nineteen twenty
#-}

twenty-one   = succ₁ twenty
twenty-two   = succ₁ twenty-one
twenty-three = succ₁ twenty-two
twenty-four  = succ₁ twenty-three
twenty-five  = succ₁ twenty-four
twenty-six   = succ₁ twenty-five
twenty-seven = succ₁ twenty-six
twenty-eight = succ₁ twenty-seven
twenty-nine  = succ₁ twenty-eight
thirty       = succ₁ twenty-nine

{-# ATP definition twenty-one twenty-two twenty-three twenty-four twenty-five
                   twenty-six twenty-seven twenty-eight twenty-nine thirty
#-}

thirty-one   = succ₁ thirty
thirty-two   = succ₁ thirty-one
thirty-three = succ₁ thirty-two
thirty-four  = succ₁ thirty-three
thirty-five  = succ₁ thirty-four
thirty-six   = succ₁ thirty-five
thirty-seven = succ₁ thirty-six
thirty-eight = succ₁ thirty-seven
thirty-nine  = succ₁ thirty-eight
forty        = succ₁ thirty-nine

{-# ATP definition thirty-one thirty-two thirty-three thirty-four thirty-five
                   thirty-six thirty-seven thirty-eight thirty-nine forty
#-}

forty-one   = succ₁ forty
forty-two   = succ₁ forty-one
forty-three = succ₁ forty-two
forty-four  = succ₁ forty-three
forty-five  = succ₁ forty-four
forty-six   = succ₁ forty-five
forty-seven = succ₁ forty-six
forty-eight = succ₁ forty-seven
forty-nine  = succ₁ forty-eight
fifty       = succ₁ forty-nine

{-# ATP definition forty-one forty-two forty-three forty-four forty-five
                   forty-six forty-seven forty-eight forty-nine fifty
#-}

fifty-one   = succ₁ fifty
fifty-two   = succ₁ fifty-one
fifty-three = succ₁ fifty-two
fifty-four  = succ₁ fifty-three
fifty-five  = succ₁ fifty-four
fifty-six   = succ₁ fifty-five
fifty-seven = succ₁ fifty-six
fifty-eight = succ₁ fifty-seven
fifty-nine  = succ₁ fifty-eight
sixty       = succ₁ fifty-nine

{-# ATP definition fifty-one fifty-two fifty-three fifty-four fifty-five
                   fifty-six fifty-seven fifty-eight fifty-nine sixty
#-}

sixty-one   = succ₁ sixty
sixty-two   = succ₁ sixty-one
sixty-three = succ₁ sixty-two
sixty-four  = succ₁ sixty-three
sixty-five  = succ₁ sixty-four
sixty-six   = succ₁ sixty-five
sixty-seven = succ₁ sixty-six
sixty-eight = succ₁ sixty-seven
sixty-nine  = succ₁ sixty-eight
seventy     = succ₁ sixty-nine

{-# ATP definition sixty-one sixty-two sixty-three sixty-four sixty-five
                   sixty-six sixty-seven sixty-eight sixty-nine seventy
#-}

seventy-one   = succ₁ seventy
seventy-two   = succ₁ seventy-one
seventy-three = succ₁ seventy-two
seventy-four  = succ₁ seventy-three
seventy-five  = succ₁ seventy-four
seventy-six   = succ₁ seventy-five
seventy-seven = succ₁ seventy-six
seventy-eight = succ₁ seventy-seven
seventy-nine  = succ₁ seventy-eight
eighty        = succ₁ seventy-nine

{-# ATP definition seventy-one seventy-two seventy-three seventy-four seventy-five
                   seventy-six seventy-seven seventy-eight seventy-nine eighty
 #-}

eighty-one   = succ₁ eighty
eighty-two   = succ₁ eighty-one
eighty-three = succ₁ eighty-two
eighty-four  = succ₁ eighty-three
eighty-five  = succ₁ eighty-four
eighty-six   = succ₁ eighty-five
eighty-seven = succ₁ eighty-six
eighty-eight = succ₁ eighty-seven
eighty-nine  = succ₁ eighty-eight
ninety       = succ₁ eighty-nine

{-# ATP definition eighty-one eighty-two eighty-three eighty-four eighty-five
                   eighty-six eighty-seven eighty-eight eighty-nine ninety
#-}

ninety-one   = succ₁ ninety
ninety-two   = succ₁ ninety-one
ninety-three = succ₁ ninety-two
ninety-four  = succ₁ ninety-three
ninety-five  = succ₁ ninety-four
ninety-six   = succ₁ ninety-five
ninety-seven = succ₁ ninety-six
ninety-eight = succ₁ ninety-seven
ninety-nine  = succ₁ ninety-eight
one-hundred  = succ₁ ninety-nine

{-# ATP definition ninety-one ninety-two ninety-three ninety-four ninety-five
                   ninety-six ninety-seven ninety-eight ninety-nine one-hundred
 #-}

hundred-one   = succ₁ one-hundred
hundred-two   = succ₁ hundred-one
hundred-three = succ₁ hundred-two
hundred-four  = succ₁ hundred-three
hundred-five  = succ₁ hundred-four
hundred-six   = succ₁ hundred-five
hundred-seven = succ₁ hundred-six
hundred-eight = succ₁ hundred-seven
hundred-nine  = succ₁ hundred-eight
hundred-ten   = succ₁ hundred-nine

{-# ATP definition hundred-one hundred-two hundred-three hundred-four hundred-five
                   hundred-six hundred-seven hundred-eight hundred-nine hundred-ten
 #-}

hundred-eleven = succ₁ hundred-ten
{-# ATP definition hundred-eleven #-}
