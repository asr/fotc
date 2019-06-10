------------------------------------------------------------------------------
-- Unary naturales numbers
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Combined.FOTC.Data.Nat.UnaryNumbers where

open import Combined.FOTC.Base

------------------------------------------------------------------------------

0'  = zero
1'  = succ₁ 0'
2'  = succ₁ 1'
3'  = succ₁ 2'
4'  = succ₁ 3'
5'  = succ₁ 4'
6'  = succ₁ 5'
7'  = succ₁ 6'
8'  = succ₁ 7'
9'  = succ₁ 8'

{-# ATP definitions 0' 1' 2' 3' 4' 5' 6' 7' 8' 9' #-}

10' = succ₁ 9'
11' = succ₁ 10'
12' = succ₁ 11'
13' = succ₁ 12'
14' = succ₁ 13'
15' = succ₁ 14'
16' = succ₁ 15'
17' = succ₁ 16'
18' = succ₁ 17'
19' = succ₁ 18'

{-# ATP definition 10' 11' 12' 13' 14' 15' 16' 17' 18' 19' #-}

20' = succ₁ 19'
21' = succ₁ 20'
22' = succ₁ 21'
23' = succ₁ 22'
24' = succ₁ 23'
25' = succ₁ 24'
26' = succ₁ 25'
27' = succ₁ 26'
28' = succ₁ 27'
29' = succ₁ 28'

{-# ATP definition 20' 21' 22' 23' 24' 25' 26' 27' 28' 29' #-}

30' = succ₁ 29'
31' = succ₁ 30'
32' = succ₁ 31'
33' = succ₁ 32'
34' = succ₁ 33'
35' = succ₁ 34'
36' = succ₁ 35'
37' = succ₁ 36'
38' = succ₁ 37'
39' = succ₁ 38'

{-# ATP definition 30' 31' 32' 33' 34' 35' 36' 37' 38' 39' #-}

40' = succ₁ 39'
41' = succ₁ 40'
42' = succ₁ 41'
43' = succ₁ 42'
44' = succ₁ 43'
45' = succ₁ 44'
46' = succ₁ 45'
47' = succ₁ 46'
48' = succ₁ 47'
49' = succ₁ 48'

{-# ATP definition 40' 41' 42' 43' 44' 45' 46' 47' 48' 49' #-}

50' = succ₁ 49'
51' = succ₁ 50'
52' = succ₁ 51'
53' = succ₁ 52'
54' = succ₁ 53'
55' = succ₁ 54'
56' = succ₁ 55'
57' = succ₁ 56'
58' = succ₁ 57'
59' = succ₁ 58'

{-# ATP definition 50' 51' 52' 53' 54' 55' 56' 57' 58' 59' #-}

60' = succ₁ 59'
61' = succ₁ 60'
62' = succ₁ 61'
63' = succ₁ 62'
64' = succ₁ 63'
65' = succ₁ 64'
66' = succ₁ 65'
67' = succ₁ 66'
68' = succ₁ 67'
69' = succ₁ 68'

{-# ATP definition 60' 61' 62' 63' 64' 65' 66' 67' 68' 69' #-}

70' = succ₁ 69'
71' = succ₁ 70'
72' = succ₁ 71'
73' = succ₁ 72'
74' = succ₁ 73'
75' = succ₁ 74'
76' = succ₁ 75'
77' = succ₁ 76'
78' = succ₁ 77'
79' = succ₁ 78'

{-# ATP definition 70' 71' 72' 73' 74' 75' 76' 77' 78' 79' #-}

80' = succ₁ 79'
81' = succ₁ 80'
82' = succ₁ 81'
83' = succ₁ 82'
84' = succ₁ 83'
85' = succ₁ 84'
86' = succ₁ 85'
87' = succ₁ 86'
88' = succ₁ 87'
89' = succ₁ 88'

{-# ATP definition 80' 81' 82' 83' 84' 85' 86' 87' 88' 89' #-}

90' = succ₁ 89'
91' = succ₁ 90'
92' = succ₁ 91'
93' = succ₁ 92'
94' = succ₁ 93'
95' = succ₁ 94'
96' = succ₁ 95'
97' = succ₁ 96'
98' = succ₁ 97'
99' = succ₁ 98'

{-# ATP definition 90' 91' 92' 93' 94' 95' 96' 97' 98' 99' #-}

100' = succ₁ 99'
101' = succ₁ 100'
102' = succ₁ 101'
103' = succ₁ 102'
104' = succ₁ 103'
105' = succ₁ 104'
106' = succ₁ 105'
107' = succ₁ 106'
108' = succ₁ 107'
109' = succ₁ 108'

{-# ATP definition 100' 101' 102' 103' 104' 105' 106' 107' 108' 109' #-}

110' = succ₁ 109'
111' = succ₁ 110'
{-# ATP definition 110' 111' #-}
