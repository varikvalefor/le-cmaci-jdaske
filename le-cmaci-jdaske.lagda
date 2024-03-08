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
\newunicodechar{𝕄}{\ensuremath{\mathnormal{\mathbb M}}}
\newunicodechar{ℕ}{\ensuremath{\mathnormal{\mathbb N}}}
\newunicodechar{ℙ}{\ensuremath{\mathnormal{\mathbb P}}}
\newunicodechar{ℚ}{\ensuremath{\mathnormal{\mathbb Q}}}
\newunicodechar{∈}{\ensuremath{\mathnormal\in}}
\newunicodechar{≡}{\ensuremath{\mathnormal\equiv}}
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
\newunicodechar{₁}{\ensuremath{_1}}
\newunicodechar{₂}{\ensuremath{_2}}
\newunicodechar{ₘ}{\ensuremath{_\AgdaFontStyle{m}}}
\newunicodechar{⦃}{\ensuremath{\mathnormal{\lbrace\!\lbrace}}}
\newunicodechar{⦄}{\ensuremath{\mathnormal{\rbrace\!\rbrace}}}

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
ni'o na mulno

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
    _∘_;
    _$_
  )
open import Data.List
  using (
    map;
    List
  )
  renaming (
    lookup to _!_
  )
open import Data.Maybe
  using (
    Maybe
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
    Eq
  )
open import Truthbrary.Record.LLC
  using (
    nu,iork;
    length;
    _∈_;
    LL;
    UL
  )

import Data.List.Relation.Unary.All
  using (
    All
  )
\end{code}

\chapter{le jicmu}

\section{la'oi .\AgdaRecord{Multiset}.}
ni'o ga jo ko'a goi la'o zoi.\ \B x\ .zoi.\ ctaipe la'o zoi.\ \AgdaRecord{Multiset} \B X\ .zoi.\ gi ga je ko'a me'oi .multiset.\ gi lo'i ro se cmima be ko'a cu du lo'i ro se cmima be la'o zoi.\ \AgdaField{Multiset.liste} \B x\ .zoi.

.i lo me'oi .multiset.\ cu smimlu lo liste  .i ku'i ro da poi ke'a me'oi .multiset.\ zo'u ro de poi ke'a .multiset.\ zo'u jitfa fa le du'u lo co'e ja se porsi cu vajni fi lo nu facki lo jei da dunli de

\begin{code}
record Multiset {a} (A : Set a) : Set a
  where
  field
    liste : List A
\end{code}

\subsection{le krinu be tu'a zo'oi .\AgdaKeyword{record}.}
ni'o le su'u la .varik.\ cu me'oi .\AgdaKeyword{record}.\ ciksi la'oi .\AgdaRecord{Multiset}.\ jenai cu gasnu lo nu la'oi .\AgdaRecord{Multiset}.\ du la'oi .\D{List}.\ cu se krinu le su'u la .varik.\ cu toldji lo nu frili fa lo nu vukna ja co'e lo ctaipe be la'o zoi.\ \AgdaRecord{Multiset} \B x\ .zoi.\ lo ctaipe be la'o zoi.\ \D{List} \B x\ .zoi.

\section{la'oi .\AgdaRecord{Selcmima}.}
ni'o la'oi .\AgdaRecord{Selcmima}.\ smimlu la'oi .\AgdaRecord{Multiset}.  .i ku'i ga jo la'o zoi.\ \B a .zoi.\ ctaipe la'o zoi.\ \AgdaRecord{Selcmima} \AgdaUnderscore .zoi.\ gi la'o zoi.\ \AgdaField{Selcmima.narpanra} \B a .zoi.\ ctaipe lo su'u ro da poi ke'a cmima ja co'e ko'a goi la'o zoi.\ \AgdaField{Selcmima.liste} \B a .zoi.\ zo'u li pa nilzilcmi lo'i ro co'e poi da du lo meirmoi be ke'a bei fo ko'a

\begin{code}
record Selcmima {a} (A : Set a) ⦃ _ : Eq A ⦄ : Set a
  where
  field
    liste : List A
    narpanra : nu,iork liste
\end{code}

\subsection{le me'oi .\AgdaKeyword{record}.\ co'e}

\subsubsection{la'o zoi.\ \AgdaPostulate{setoidSelcmima}.}
ni'o la .varik.\ cu stidi lo nu tcidu le velcki fa lo na jimpe\ldots kei je cu stidi lo nu tadni la'oi .Agda.\ fa lo na jimpe be fi le velcki

\begin{code}
setoidSelcmima : ∀ {a} → {A : Set a} → ⦃ Eq A ⦄ → Setoid a a
setoidSelcmima {A = A} = record {
  Carrier = Selcmima A;
  _≈_ = λ a b → Al (_∈ L b) (L a) × Al (_∈ L a) (L b);
  isEquivalence = {!!}}
  where
  L = Selcmima.liste
  Al = Data.List.Relation.Unary.All.All
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
ni'o ga jo ko'a goi la'o zoi.\ \B a .zoi.\ ctaipe la'o zoi.\ \AgdaRecord{Jdanunza'omro} .zoi.\ gi ga je ko'a jdanuza'omro gi\ldots
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

\section{la'oi .\AgdaRecord{Prenu}.}
ni'o ga jo ko'a goi la'o zoi.\ \B a .zoi.\ ctaipe la'oi .\AgdaRecord{Prenu}.\ gi\ldots
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

\section{la'oi .\AgdaRecord{Lijda}.}
ni'o ga jo ko'a goi la'o zoi.\ \B a .zoi.\ ctaipe la'oi .\AgdaRecord{Lijda}.\ gi\ldots
\begin{itemize}
	\item ga je la'o zoi.\ \AgdaField{Lijda.marde} \B a .zoi.\ marde lo ro seljda be ko'a\footnote{.i jitfa fa le du'u ro da zo'u da srana lo marde be da be'o jo lo marde be lo ro seljda be lo lijda be da  .i su'o da zo'u su'o de zo'u ga je de pagbu lo marde be da gi su'o di poi lijda ke'a fa lo lijda be da zo'u de pagbu lo marde be da be'o jenai lo marde be di} gi
	\item ga je ga jonai la'oi .\AgdaInductiveConstructor{nothing}.\ du ko'e goi la'o zoi.\ \F{mapₘ} \AgdaField{Selcmima.liste} \OpF \$ \AgdaField{Lijda.jdanunza'omro} \B a .zoi.\ gi ga je su'o da zo'u da jdanunza'omro fi ko'a gi ko'e me'oi .\AgdaInductiveConstructor{just}.\ lo'i jdanunza'omro be fi ko'a gi
	\item ga jonai\ldots
	\begin{itemize}
		\item la'oi .\AgdaInductiveConstructor{nothing}.\ du ko'e goi la'o zoi.\ \AgdaField{Lijda.cevni} \B a .zoi.\ gi
		\item ga je selcei fa lo ro seljda be ko'a gi\ldots
		\begin{itemize}
			\item ga je ko'e me'oi .\AgdaInductiveConstructor{just}.\ lo'i cevni be ko'a gi
			\item ga jo la'o zoi.\ \B t\ .zoi.\ ctaipe la'o zoi.\ \F{Is-just} \OpF \$ \AgdaField{Lijda.cevni} \B a\ .zoi.\ gi ga jo la'o zoi.\ \B Z\ .zoi.\ du la'o zoi.\ \F{Data.Maybe.to-witness} \B t\ .zoi.\ gi la'o zoi.\ \Sym(proj₂ \B Z\Sym) \B m \B n\ .zoi.\ co'e ja ni la'o zoi.\ \AgdaField{proj₁} \OpF \Sym(\AgdaField{proj₁} \B Z\Sym) \OpF !\ \B m .zoi.\ nelci la'o zoi.\ \AgdaField{proj₁} \OpF \Sym(\AgdaField{proj₁} \B Z\Sym) \OpF !\ \B n .zoi.
		\end{itemize}
	\end{itemize}
\end{itemize}

% ni'o xu cadga fa lo nu la .varik. cu ciksi lo co'e ja ctaipe be le su'u pilno la'o zoi. UL $ List Prenu .zoi. jenai la'o zoi. Selcmima Prenu .zoi.

\begin{code}
record Lijda : Set
  where
  private
    𝔽L : ∀ {a} → {A : Set a}
       → ⦃ Q : LL A ⦄ → ⦃ _ : Eq $ LL.e Q ⦄
       → UL A → Set
    𝔽L = Fin ∘ length ∘ proj₁
  field
    cevni : Maybe $ Σ (UL $ List Prenu) $ (λ X → X → X → ℚ) ∘ 𝔽L
    marde : Marde
    jdanunza'omro : Maybe $ Selcmima Jdanunza'omro
\end{code}
\end{document}
