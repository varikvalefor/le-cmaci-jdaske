\documentclass{report}

\usepackage{ar}
\usepackage[bw]{agda}
\usepackage{ifsym}
\usepackage{amsmath}
\usepackage{amssymb}
\usepackage{parskip}
\usepackage{mathabx}
\usepackage{unicode-math}
\usepackage{newunicodechar}

\newunicodechar{λ}{\ensuremath{\mathnormal\lambda}}
\newunicodechar{∷}{\ensuremath{\mathnormal\Colon}}
\newunicodechar{∨}{\ensuremath{\mathnormal\vee}}
\newunicodechar{𝔹}{\ensuremath{\mathnormal{\mathbb B}}}
\newunicodechar{𝔽}{\ensuremath{\mathnormal{\mathbb F}}}
\newunicodechar{𝕃}{\ensuremath{\mathnormal{\mathbb L}}}
\newunicodechar{𝕄}{\ensuremath{\mathnormal{\mathbb M}}}
\newunicodechar{ℕ}{\ensuremath{\mathnormal{\mathbb N}}}
\newunicodechar{ℙ}{\ensuremath{\mathnormal{\mathbb P}}}
\newunicodechar{ℚ}{\ensuremath{\mathnormal{\mathbb Q}}}
\newunicodechar{∈}{\ensuremath{\mathnormal\in}}
\newunicodechar{∉}{\ensuremath{\mathnormal\notin}}
\newunicodechar{⟨}{\ensuremath{\mathnormal\langle}}
\newunicodechar{⟩}{\ensuremath{\mathnormal\rangle}}
\newunicodechar{≡}{\ensuremath{\mathnormal\equiv}}
\newunicodechar{≢}{\ensuremath{\mathnormal\nequiv}}
\newunicodechar{∎}{\ensuremath{\mathnormal\blacksquare}}
\newunicodechar{≈}{\ensuremath{\mathnormal\approx}}
\newunicodechar{∶}{\ensuremath{\mathnormal\colon\!\!}}
\newunicodechar{ν}{\ensuremath{\mathnormal\nu}}
\newunicodechar{μ}{\ensuremath{\mathnormal\mu}}
\newunicodechar{∸}{\ensuremath{\mathnormal\dotdiv}}
\newunicodechar{ᵇ}{\ensuremath{\mathnormal{^\AgdaFontStyle{b}}}}
\newunicodechar{≥}{\ensuremath{\mathnormal\geq}}
\newunicodechar{ϕ}{\ensuremath{\mathnormal\phi}}
\newunicodechar{∧}{\ensuremath{\mathnormal\wedge}}
\newunicodechar{∣}{\ensuremath{\mathnormal{|}}}
\newunicodechar{∘}{\ensuremath{\mathnormal\circ}}
\newunicodechar{∀}{\ensuremath{\mathnormal\forall}}
\newunicodechar{ℓ}{\ensuremath{\mathnormal\ell}}
\newunicodechar{σ}{\ensuremath{\mathnormal\sigma}}
\newunicodechar{α}{\ensuremath{\mathnormal\alpha}}
\newunicodechar{₁}{\ensuremath{\mathnormal{_1}}}
\newunicodechar{₂}{\ensuremath{\mathnormal{_2}}}
\newunicodechar{ₘ}{\ensuremath{_\AgdaFontStyle{m}}}
\newunicodechar{⦃}{\ensuremath{\mathnormal{\lbrace\hspace{-0.3em}|}}}
\newunicodechar{⦄}{\ensuremath{\mathnormal{|\hspace{-0.3em}\rbrace}}}
\newunicodechar{≟}{\ensuremath{\mathnormal{\stackrel{?}{=}}}}

\newcommand\Sym\AgdaSymbol
\newcommand\D\AgdaDatatype
\newcommand\F\AgdaFunction
\newcommand\B\AgdaBound
% | ni'o cadga fa lo nu la'oi .BlS. mo  .i selneimau fi la .varik.
\newcommand\OpF[1]{\AgdaOperator{\AgdaFunction{#1}}}

\title{le cmaci jdaske}
\author{la .varik.\ .VALefor.}

\begin{document}

\maketitle

\tableofcontents

\chapter{le me'oi .disclaimer.}
ni'o na mulno  .i la .varik.\ cu stidi lo nu na ci'au .ue sai lo nu vo'a mutce lo ka ce'u bixygau pe'a

\chapter{le vrici}

\begin{code}
open import Data.Fin
  using (
    Fin
  )
open import Data.Nat
  using (
    ℕ
  )
open import Function
  using (
    _∘₂_;
    _on_;
    flip;
    _∘_;
    _$_
  )
open import Data.Bool
  using (
    not;
    T?
  )
open import Data.List
  as 𝕃
  using (
    map;
    zip;
    List
  )
  renaming (
    lookup to _!_
  )
open import Data.Empty
  using (
    ⊥
  )
open import Data.Maybe
  using (
    nothing;
    Maybe;
    just
  )
  renaming (
    map to mapₘ
  )
open import Data.String
  using (
    String
  )
open import Data.Product
  using (
    Σ;
    _×_;
    _,_;
    proj₁;
    proj₂
  )
open import Data.Rational
  using (
    ℚ
  )
open import Relation.Binary
  using (
    Setoid
  )
open import Truthbrary.Record.Eq
  using (
    _≡ᵇ_;
    _≟_;
    Eq
  )
open import Truthbrary.Record.LLC
  using (
    nu,iork;
    length;
    _∉_;
    _∈_;
    LL;
    UL
  )
open import Relation.Binary.PropositionalEquality
  using (
    refl;
    _≡_
  )

import Data.List.Relation.Unary.All
  as LUA
  using (
    _∷_;
    All;
    []
  )
\end{code}

\chapter{le vrici je fancu}

\section{la .\F{cmimakonk}.}
ni'o la .\F{cmimakonk}.\ ctaipe le su'u ro da poi ke'a co'e zo'u ro de poi ke'a co'e zo'u da cmima lo konkatena be da bei de

\begin{code}
cmimakonk : ∀ {a} → {A : Set a}
          → ⦃ _ : Eq A ⦄
          → (x : A)
          → (xs : List A)
          → x ∈_ $ x 𝕃.∷ xs
cmimakonk x xs = sym $ begin
  length (𝕃.take 1 $ 𝕃.filter (_≟_ x) $ x 𝕃.∷ _) ≡⟨ {!!} ⟩
  1 ∎
  where
  open import Relation.Binary.PropositionalEquality
  open ≡-Reasoning
\end{code}

\section{la .\F{cmimapred}.}
ni'o la .\F{cmimapred}.\ ctaipe le su'u ro da poi ke'a co'e zo'u ro de poi ke'a co'e zo'u ro di poi ke'a co'e zo'u da cmima di naja lo konkatena be de bei di

\begin{code}
cmimapred : ∀ {a} → {A : Set a}
          → ⦃ _ : Eq A ⦄
          → (x z : A)
          → (xs : List A)
          → x ∈ xs
          → x ∈_ $ z 𝕃.∷ xs
cmimapred = {!!}
\end{code}

\section{la'oi .\F{Dun}.}
ni'o xu sarcu fa lo nu ciksi bau la .lojban.

\begin{code}
Dun : ∀ {a} → {A : Set a}
    → ⦃ Eq A ⦄
    → (x z : List A)
    → Set a
Dun x z = LUA.All (_∈ x) z × LUA.All (_∈ z) x
\end{code}

\subsection{le ctaipe be zo'e ja le su'u la'oi .\F{Dun}.\ mapti}

\begin{code}
module DunVeritasJaZo'e where
  T : ∀ {a} → {A : Set a}
    → ⦃ _ : Eq A ⦄
    → {i j k : List A}
    → Dun i j
    → Dun j k
    → Dun i k
  T = {!!}
\end{code}
\section{la'oi .\F{nu,iorks}.}
ni'o ro da zo'u da cmima la'o zoi.\ \F{nu,iorks} \B x\ .zoi.\ jo cu du lo su'o cmima be la'oi .\B x.

\begin{code}
nu,iorks : ∀ {a} → {A : Set a} → ⦃ _ : Eq A ⦄ → List A → List A
nu,iorks 𝕃.[] = 𝕃.[]
nu,iorks (x 𝕃.∷ z) = x 𝕃.∷ 𝕃.filter (_≢?_ x) (nu,iorks z)
  where
  _≢?_ = T? ∘₂ not ∘₂ _≡ᵇ_
\end{code}

\subsection{le ctaipe be le su'u mapti}

\begin{code}
module Nu,iorksVeritas where
  pav : ∀ {a} → {A : Set a}
      → ⦃ _ : Eq A ⦄
      → (x : List A)
      → nu,iork $ nu,iorks x
  pav 𝕃.[] = refl
  pav (x 𝕃.∷ xs) = nuk {!!} $ filnek x $ nu,iorks xs
    where
    filnek : ∀ {a} → {A : Set a}
           → ⦃ _ : Eq A ⦄
           → (e : A)
           → (x : List A)
           → e ∉ 𝕃.filter (T? ∘ not ∘ _≡ᵇ_ e) x
    filnek e 𝕃.[] = refl
    filnek e (x 𝕃.∷ xs) = {!!}
    nuk : ∀ {a} → {A : Set a}
        → ⦃ _ : Eq A ⦄
        → {e : A}
        → {x : List A}
        → nu,iork x
        → e ∉ x
        → nu,iork $ e 𝕃.∷ x
    nuk = {!!}

  rel : ∀ {a} → {A : Set a}
      → ⦃ _ : Eq A ⦄
      → (x : List A)
      → (e : A)
      → e ∈ x → e ∈ nu,iorks x
  rel = {!!}

  cib : ∀ {a} → {A : Set a}
      → ⦃ _ : Eq A ⦄
      → (x : List A)
      → (e : A)
      → e ∈ nu,iorks x → e ∈ x
  cib = {!!}
\end{code}

\section{la \F{girzu}}
ni'o ga jo la'oi .\B{G}.\ du la'o zoi.\ \F{map} \AgdaField{proj₁} \OpF \$ \F{girzu} \B g\ .zoi.\ gi ro da poi ke'a cmima la'oi .\B{G}.\ zo'u ga je cmima la'oi .\B{g}.\ lo te orsi be da gi lo ve .orsi be da cu du lo co'e ja nilzilcmi be lo'i ro cmima be la'oi .\B{G}.\ .zoi.\ poi ke'a du lo te .orsi be da

\begin{code}
girzu : ∀ {a} → {A : Set a}
      → ⦃ _ : Eq A ⦄
      → List A
      → List $ A × ℕ
girzu L = (zipmap $ length ∘ flip F L) $ nu,iorks L
  where
  zipmap = λ f x → zip x $ map f x
  F = λ a → length ∘ 𝕃.filter (_≟ a)
\end{code}

\subsection{le ctaipe be le su'u la \F{girzu}\ cu mapti}

\begin{code}
module GirzuVeritas where
  pav : ∀ {a} → {A : Set a}
      → ⦃ _ : Eq A ⦄
      → (L : List A)
      → (flip LUA.All (girzu L)
          (λ (x₁ , x₂) →
            (_×_
              (x₁ ∈ L)
              (x₂ ≡_ $ length $ 𝕃.filter (_≟ x₁) L))))
  pav 𝕃.[] = LUA.[]
  pav (x 𝕃.∷ xs) = (cmimakonk x xs , refl) LUA.∷ {!!}

  rel : ∀ {a} → {A : Set a}
      → ⦃ _ : Eq A ⦄
      → (L : List A)
      → flip LUA.All L $ _∈ 𝕃.map proj₁ (girzu L)
  rel 𝕃.[] = LUA.All.[]
  rel (x 𝕃.∷ xs) = girzu₁ x xs LUA.All.∷ {!!}
    where
    girzu₁ : ∀ {a} → {A : Set a}
           → ⦃ _ : Eq A ⦄
           → (x : A)
           → (xs : List A)
           → x ∈ map proj₁ (girzu $ x 𝕃.∷ xs)
    girzu₁ = {!!}

  sum : ∀ {a} → {A : Set a}
      → ⦃ _ : Eq A ⦄
      → (L : List A)
      → 𝕃.sum (𝕃.map proj₂ $ girzu L) ≡ length L
  sum 𝕃.[] = refl
  sum (x 𝕃.∷ xs) = {!!}
\end{code}

\subsection{la .\F{prefif}.}
ni'o xu sarcu fa lo nu ciksi bau la .lojban.

\begin{code}
prefif : ∀ {a} → {A : Set a}
       → ⦃ _ : Eq A ⦄
       → (x : A)
       → (xs : List A)
       → LUA.All (_∈ (x 𝕃.∷ xs)) xs
prefif x 𝕃.[] = {!!}
prefif e (x 𝕃.∷ xs) = {!!}
\end{code}

\section{la .\F{refif}.}
ni'o xu sarcu fa lo nu ciksi bau la .lojban.

\begin{code}
refif : ∀ {a} → {A : Set a}
      → ⦃ _ : Eq A ⦄
      → (x : List A)
      → LUA.All (_∈ x) x
refif 𝕃.[] = LUA.[]
refif (x 𝕃.∷ z) = cmimakonk x z LUA.∷ prefif x z
\end{code}

\chapter{le jicmu}

\section{la'oi .\AgdaRecord{Multiset}.}
ni'o ga jo ko'a goi la'oi .\B{x}.\ ctaipe la'o zoi.\ \AgdaRecord{Multiset} \B X\ .zoi.\ gi ga je ko'a me'oi .multiset.\ gi lo'i ro se cmima be ko'a cu du lo'i ro se cmima be la'o zoi.\ \AgdaField{Multiset.liste} \B x\ .zoi.

.i lo me'oi .multiset.\ cu smimlu lo liste  .i ku'i ro da poi ke'a me'oi .multiset.\ zo'u ro de poi ke'a .multiset.\ zo'u jitfa fa le du'u lo co'e ja se porsi cu vajni fi lo nu facki lo jei da dunli de

\begin{code}
record Multiset {a} (A : Set a) : Set a
  where
  field
    liste : List A
\end{code}

\subsection{le krinu be tu'a zo'oi .\AgdaKeyword{record}.}
ni'o la .varik.\ cu me'oi .\AgdaKeyword{record}.\ ciksi la'oi .\AgdaRecord{Multiset}.\ jenai cu gasnu lo nu la'oi .\AgdaRecord{Multiset}.\ du la'oi .\D{List}.  .i krinu la'e di'u fa le su'u la .varik.\ cu toldji lo nu frili fa lo nu vukna ja co'e lo ctaipe be la'o zoi.\ \AgdaRecord{Multiset} \B x\ .zoi.\ lo ctaipe be la'o zoi.\ \D{List} \B x\ .zoi.

\subsection{le me'oi .\AgdaKeyword{record}.\ co'e}

\subsubsection{la'o zoi.\ \F{setoidMultiset}\ .zoi.}

\begin{code}
setoidMultiset : ∀ {a} → {A : Set a} → ⦃ Eq A ⦄ → Setoid a a
setoidMultiset {A = A} = record {
  Carrier = Multiset A;
  _≈_ = Dun on GL;
  isEquivalence = record {
    refl = (λ x → x , x) $ refif _;
    sym = Data.Product.swap;
    trans = T}}
  where
  open DunVeritasJaZo'e using (T)
  GL = girzu ∘ Multiset.liste
\end{code}

\section{la'oi .\AgdaRecord{Selcmima}.}
ni'o la'oi .\AgdaRecord{Selcmima}.\ smimlu la'oi .\AgdaRecord{Multiset}.  .i ku'i ga jo la'oi .\B{a}.\ ctaipe la'o zoi.\ \AgdaRecord{Selcmima} \AgdaUnderscore .zoi.\ gi la'o zoi.\ \AgdaField{Selcmima.narpanra} \B a .zoi.\ ctaipe lo su'u ro da poi ke'a cmima ja co'e ko'a goi la'o zoi.\ \AgdaField{Selcmima.liste} \B a .zoi.\ zo'u li pa nilzilcmi lo'i ro co'e poi da du lo meirmoi be ke'a bei fo ko'a

\begin{code}
record Selcmima {a} (A : Set a) ⦃ _ : Eq A ⦄ : Set a
  where
  field
    liste : List A
    narpanra : nu,iork liste
\end{code}

\subsection{le me'oi .\AgdaKeyword{record}.\ co'e}

\subsubsection{la'o zoi.\ \F{setoidSelcmima}\ .zoi.}
ni'o la .varik.\ cu stidi lo nu tcidu le velcki fa lo na jimpe\ldots kei je cu stidi lo nu tadni la'oi .Agda.\ fa lo na jimpe be fi le velcki

\begin{code}
setoidSelcmima : ∀ {a} → {A : Set a} → ⦃ Eq A ⦄ → Setoid a a
setoidSelcmima {A = A} = record {
  Carrier = Selcmima A;
  _≈_ = λ a b → Al (_∈ L b) (L a) × Al (_∈ L a) (L b);
  isEquivalence = record {
    refl = λ {x} → (λ x → x , x) $ refif $ Selcmima.liste x;
    sym = Data.Product.swap;
    trans = {!!}}}
  where
  L = Selcmima.liste
  Al = LUA.All
\end{code}

\section{la'oi .\AgdaPostulate{Fasnu}.}
ni'o ro da zo'u da ctaipe la'oi .\AgdaPostulate{Fasnu}.\ jo cu fasnu

\begin{code}
postulate Fasnu : Set
\end{code}

\subsection{le me'oi .\AgdaKeyword{instance}.}

\begin{code}
postulate instance eqFasnu : Eq Fasnu
\end{code}

\section{la'oi .\AgdaPostulate{Selpre}.}
ni'o ro da zo'u da ctaipe la'oi .\AgdaPostulate{Selpre}.\ jo cu selpre

\begin{code}
postulate Selpre : Set
\end{code}

\subsection{le me'oi .\AgdaKeyword{instance}.}

\begin{code}
postulate instance eqSelpre : Eq Selpre
\end{code}

\chapter{le srana be lo lijda ja co'e}

\section{la'oi .\AgdaRecord{Jdanunza'omro}.}
ni'o ga jo ko'a goi la'oi .\B{a}.\ ctaipe la'oi .\AgdaRecord{Jdanunza'omro}.\ gi ga je ko'a jdanuza'omro gi\ldots
\begin{itemize}
	\item ga je ko'a selcme lo ro cmima be la'o zoi.\ \AgdaField{Jdanunza'omro.cmene} \B a .zoi.\ gi
	\item krici le du'u\ldots
	\begin{itemize}
		\item ga je ro da zo'u da selvau la'o zoi.\ \AgdaField{Selcmima.liste} \OpF \$ \AgdaField{Jdanunza'omro.velski} \B a .zoi.\ jo cu jetnu je cu velski ko'a gi
		\item ko'a jdanunza'omro lo ro prenu poi ke'a zukte lo cmima be la'o zoi.\ \AgdaField{Selcmima.liste} \OpF \$ \AgdaField{Jdanunza'omro.krinu} \B a .zoi.
	\end{itemize}
\end{itemize}

\begin{code}
record Jdanunza'omro : Set
  where
  field
    cmene : Selcmima String
    velski : Selcmima Fasnu
    krinu : Selcmima Fasnu
\end{code}

\subsection{le me'oi .\AgdaKeyword{instance}.}

\begin{code}
postulate instance eqJdanunza'omro : Eq Jdanunza'omro
\end{code}

\section{la'oi .\F{Marde}.}
ni'o ga naja la'oi .\F{f}.\ ctaipe la'oi .\F{Marde}.\ gi la'o zoi.\ \F f \B x\ .zoi.\ ni la'oi .\B{x}.\ vrude la'oi .\F{f}.  .i ro da zo'u ga jo la'oi .\F{f}.\ ctaipe la'oi .\F{Marde}.\ gi ga jo li no du lo me'oi .\F{f}.\ be da gi na'e ke co'e ja krici fi da fa lo ro prenu poi la'oi .\F{f}.\ du lo ro marde be ke'a

\begin{code}
Marde : Set
Marde = Fasnu → ℚ
\end{code}

\subsection{le me'oi .\AgdaKeyword{instance}.}

\begin{code}
postulate instance eqMarde : Eq Marde
\end{code}

\subsection{le me'oi .\AgdaKeyword{record}.\ co'e}

\subsubsection{la'oi .\F{setoidMarde}.}

\begin{code}
setoidMarde : Setoid _ _
setoidMarde = record {
  Carrier = Marde;
  _≈_ = λ a b → (z : Fasnu) → a z ≡ b z;
  isEquivalence = record {
    refl = λ z → refl;
    sym = λ {a b} x z → {!!};
    trans = {!!}}}
\end{code}

\section{la'oi .\AgdaRecord{Prenu}.}
ni'o ga jo ko'a goi la'oi .\B{a}.\ ctaipe la'oi .\AgdaRecord{Prenu}.\ gi\ldots
\begin{itemize}
	\item ga je cmene ko'a fa lo ro cmima be la'o zoi.\ \AgdaField{Selcmima.liste} \OpF \$ \AgdaField{Prenu.cmene} \B a .zoi.\ gi
	\item ga je la'o zoi.\ \AgdaField{Prenu.marde} \B a .zoi.\ marde ko'a gi
	\item la'o zoi.\ \AgdaField{Prenu.selpre} \B a .zoi.\ selpre ko'a
\end{itemize}

\begin{code}
record Prenu : Set
  where
  field
    cmene : Selcmima String
    marde : Marde
    selpre : Selpre
\end{code}

\subsection{le su'u na me'oi .\AgdaKeyword{field}.\ fa lo srana be lo lijda}
ni'o la .varik.\ cu djica ko'a goi lo nu su'o da zo'u da me'oi .\AgdaKeyword{field}.\ la'oi .\AgdaRecord{Prenu}.\ je cu ctaipe ja co'e la'oi .\AgdaRecord{Lijda}.  .i ku'i la .varik.\ cu na birti lo du'u ma kau zabna je su'u rinka ja co'e ko'a  .i ga je le velcki be la'oi .\AgdaRecord{Prenu}.\ cu lidne le velcki be la'oi .\AgdaRecord{Lijda}.\ gi zmadu fi le ka ce'u seldji la .varik.\ fa lo nu lo me'oi .\AgdaKeyword{field}.\ be la'oi .\AgdaRecord{Lijda}.\ cu srana lo prenu kei fe lo nu lo me'oi .\AgdaKeyword{field}.\ be la'oi .\AgdaRecord{Prenu}.\ cu srana lo lijda

.i la .varik.\ cu djica curmi lo nu stidi

\subsection{le me'oi .\AgdaKeyword{instance}.}

\begin{code}
postulate instance eqPrenu : Eq Prenu
\end{code}

\subsection{le me'oi .\AgdaKeyword{record}.\ co'e}

\subsubsection{la'oi .\F{setoidPrenu}.}

\begin{code}
setoidPrenu : (λ x → Setoid x x) _
setoidPrenu = record {
  Carrier = Prenu;
  _≈_ = {!!};
  isEquivalence = {!!}}
\end{code}

\section{la'oi .\AgdaRecord{Lijda}.}
ni'o ga jo ko'a goi la'oi .\B{a}.\ ctaipe la'oi .\AgdaRecord{Lijda}.\ gi\ldots
\begin{itemize}
	\item ga je la'o zoi.\ \AgdaField{Lijda.marde} \B a .zoi.\ marde lo ro seljda be ko'a\footnote{.i jitfa fa le du'u ro da zo'u da srana lo marde be da be'o jo lo marde be lo ro seljda be lo lijda be da  .i su'o da zo'u su'o de zo'u ga je de pagbu lo marde be da gi su'o di poi ke'a seljda lo lijda be da zo'u de pagbu lo marde be da be'o jenai lo marde be di} gi
	\item ga je ga jonai la'oi .\AgdaInductiveConstructor{nothing}.\ du ko'e goi la'o zoi.\ \F{mapₘ} \AgdaField{Selcmima.liste} \OpF \$ \AgdaField{Lijda.jdanunza'omro} \B a .zoi.\ gi ga je su'o da zo'u da jdanunza'omro fi ko'a gi ko'e me'oi .\AgdaInductiveConstructor{just}.\ lo'i jdanunza'omro be fi ko'a gi
	\item ga jonai\ldots
	\begin{itemize}
		\item la'oi .\AgdaInductiveConstructor{nothing}.\ du ko'e goi la'o zoi.\ \AgdaField{Lijda.cevni} \B a .zoi.\ gi
		\item ga je selcei fa lo ro seljda be ko'a gi\ldots
		\begin{itemize}
			\item ga je ko'e me'oi .\AgdaInductiveConstructor{just}.\ lo'i cevni be ko'a gi
			\item ga jo la'oi .\B{t}.\ ctaipe la'o zoi.\ \F{Is-just} \OpF \$ \AgdaField{Lijda.cevni} \B a\ .zoi.\ gi ga jo la'oi .\B{Z}.\ du la'o zoi.\ \F{Data.Maybe.to-witness} \B t\ .zoi.\ gi ga jo la'oi .\B{G}.\ du la'o zoi.\ \AgdaField{proj₁} \OpF \$ \AgdaField{proj₁} \B Z\ .zoi.\ gi lo mu'oi zoi.\ \Sym(proj₂ \B Z\Sym) \B m \B n\ .zoi.\ be ko'a goi la'o zoi.\ \B G \OpF !\ \B m .zoi.\ bei ko'e goi la'o zoi.\ \B G \OpF !\ \B n .zoi.\ cu co'e ja ni ko'a nelci ko'e
		\end{itemize}
	\end{itemize}
\end{itemize}

% ni'o xu cadga fa lo nu la .varik. cu ciksi lo co'e ja ctaipe be le su'u pilno la'o zoi. UL $ List Prenu .zoi. jenai la'o zoi. Selcmima Prenu .zoi.
% .i lakne  .i la .varik. cu cusku dei ca le nu la .varik. na morji lo du'u ma kau krinu

\begin{code}
record Lijda : Set
  where
  private
    𝔽L : ∀ {a b} → {A : Set a} → {B : A → Set b}
       → ⦃ LL A ⦄
       → Σ A B → Set
    𝔽L = Fin ∘ length ∘ proj₁
  field
    cevni : Maybe $ Σ (UL $ List Prenu) $ (λ X → X → X → ℚ) ∘ 𝔽L
    marde : Marde
    jdanunza'omro : Maybe $ Selcmima Jdanunza'omro
\end{code}

\subsection{le me'oi .\AgdaKeyword{record}.\ co'e}

\begin{code}
setoidLijda : (λ x → Setoid x x) _
setoidLijda = record {
  Carrier = Lijda;
  _≈_ = λ a b → Lijda.marde a ≡ Lijda.marde b
              × Setoid._≈_ SLJ (LJ a) (LJ b)
              × {!!};
  isEquivalence = {!!} }
  where
  LJ = Lijda.jdanunza'omro
  SLJ : (λ x → Setoid x x) _
  SLJ = record {
    Carrier = Maybe $ Selcmima Jdanunza'omro;
    _≈_ = SLJdu;
    isEquivalence = {!!}}
    where
    SLJdu : (λ x → x → x → Set) _
    SLJdu a@nothing b@nothing = a ≡ b
    SLJdu nothing _ = ⊥
    SLJdu _ nothing = ⊥
    SLJdu (just a) (just b) = Setoid._≈_ setoidSelcmima a b
\end{code}
\end{document}
