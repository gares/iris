Here we collect some information on how to set up your editor to properly input
and output the unicode characters used throughout Iris.

## General: Unicode Fonts

Most editors will just use system fonts for rendering unicode characters and do
not need further configuration once the fonts are installed.  Here are some
combinations of fonts that are known to give readable results (i.e., each of
these sets of fonts covers all the required characters):

* Fira Mono, DejaVu Mono, Symbola

## Emacs

### Unicode Input

First, install `math-symbol-lists` by doing `M-x package-install math-symbol-lists`.

Next, add the following to your `~/.emacs` to configure an input method based
on the math symbol list, and with some custom aliases for symbols used a lot in Iris:
```
;; Input of unicode symbols
(require 'math-symbol-lists)
; Automatically use math input method for Coq files
(add-hook 'coq-mode-hook (lambda () (set-input-method "math")))
; Input method for the minibuffer
(defun my-inherit-input-method ()
  "Inherit input method from `minibuffer-selected-window'."
  (let* ((win (minibuffer-selected-window))
         (buf (and win (window-buffer win))))
    (when buf
      (activate-input-method (buffer-local-value 'current-input-method buf)))))
(add-hook 'minibuffer-setup-hook #'my-inherit-input-method)
; Define the actual input method
(quail-define-package "math" "UTF-8" "Ω" t)
(quail-define-rules ; add whatever extra rules you want to define here...
 ("\\fun"    ?λ)
 ("\\mult"   ?⋅)
 ("\\ent"    ?⊢)
 ("\\valid"  ?✓)
 ("\\diamond" ?◇)
 ("\\box"    ?□)
 ("\\bbox"   ?■)
 ("\\later"  ?▷)
 ("\\pred"   ?φ)
 ("\\and"    ?∧)
 ("\\or"     ?∨)
 ("\\comp"   ?∘)
 ("\\ccomp"  ?◎)
 ("\\all"    ?∀)
 ("\\ex"     ?∃)
 ("\\to"     ?→)
 ("\\sep"    ?∗)
 ("\\lc"     ?⌜)
 ("\\rc"     ?⌝)
 ("\\Lc"     ?⎡)
 ("\\Rc"     ?⎤)
 ("\\lam"    ?λ)
 ("\\empty"  ?∅)
 ("\\Lam"    ?Λ)
 ("\\Sig"    ?Σ)
 ("\\-"      ?∖)
 ("\\aa"     ?●)
 ("\\af"     ?◯)
 ("\\auth"   ?●)
 ("\\frag"   ?◯)
 ("\\iff"    ?↔)
 ("\\gname"  ?γ)
 ("\\incl"   ?≼)
 ("\\latert" ?▶)
 ("\\update" ?⇝)

 ;; accents (for iLöb)
 ("\\\"o" ?ö)

 ;; subscripts and superscripts
 ("^^+" ?⁺) ("__+" ?₊) ("^^-" ?⁻)
 ("__0" ?₀) ("__1" ?₁) ("__2" ?₂) ("__3" ?₃) ("__4" ?₄)
 ("__5" ?₅) ("__6" ?₆) ("__7" ?₇) ("__8" ?₈) ("__9" ?₉)

 ("__a" ?ₐ) ("__e" ?ₑ) ("__h" ?ₕ) ("__i" ?ᵢ) ("__k" ?ₖ)
 ("__l" ?ₗ) ("__m" ?ₘ) ("__n" ?ₙ) ("__o" ?ₒ) ("__p" ?ₚ)
 ("__r" ?ᵣ) ("__s" ?ₛ) ("__t" ?ₜ) ("__u" ?ᵤ) ("__v" ?ᵥ) ("__x" ?ₓ)
)
(mapc (lambda (x)
        (if (cddr x)
            (quail-defrule (cadr x) (car (cddr x)))))
      (append math-symbol-list-basic math-symbol-list-extended))
```

Finally, set your default input method with `M-x customize-set-value`, setting
`default-input-method` to `math`.

### Font Configuration

Even when usable fonts are installed, Emacs tends to pick bad fonts for some
symbols like universal and existential quantifiers.  The following configuration
results in a decent choice for the symbols used in Iris:

```
;; Fonts
(set-face-attribute 'default nil :height 110) ; height is in 1/10pt
(dolist (ft (fontset-list))
  ; Main font
  (set-fontset-font ft 'unicode (font-spec :name "Monospace"))
  ; Fallback font
  ; Appending to the 'unicode list makes emacs unbearably slow.
  ;(set-fontset-font ft 'unicode (font-spec :name "DejaVu Sans Mono") nil 'append)
  (set-fontset-font ft nil (font-spec :name "DejaVu Sans Mono"))
)
; Fallback-fallback font
; If we 'append this to all fontsets, it picks Symbola even for some cases where DejaVu could
; be used. Adding it only to the "t" table makes it Do The Right Thing (TM).
(set-fontset-font t nil (font-spec :name "Symbola"))
```

## CoqIDE 8.9 and earlier on Linux (ibus-m17n)

On Linux with old versions of CoqIDE you can use the Intelligent
Input Bus (IBus) framework to input Unicode symbols. First, install `ibus-m17n`
via your system's package manager. Next, create a file `~/.m17n.d/coq.mim` to
configure an input method based on the math symbol list, and with some custom
aliases for symbols used a lot in Iris:

```
;; Usage: copy to ~/.m17n.d/coq.mim

(input-method t coq)
(description "Input method for Coq")
(title "Coq")

(map (trans

;; Standard LaTeX math notations
  ("\\forall"         "∀")
  ("\\exists"         "∃")
  ("\\lam"            "λ")
  ("\\not"            "¬")
  ("\\/"              "∨")
  ("/\\"              "∧")
  ("->"               "→")
  ("<->"              "↔")
  ("\\<-"             "←") ;; we add a backslash because the plain <- is used for the rewrite tactic
  ("\\=="             "≡")
  ("\\/=="            "≢")
  ("/="               "≠")
  ("<="               "≤")
  ("\\in"             "∈")
  ("\\notin"          "∉")
  ("\\cup"            "∪")
  ("\\cap"            "∩")
  ("\\setminus"       "∖")
  ("\\subset"         "⊂")
  ("\\subseteq"       "⊆")
  ("\\sqsubseteq"     "⊑")
  ("\\sqsubseteq"     "⊑")
  ("\\notsubseteq"    "⊈")
  ("\\meet"           "⊓")
  ("\\join"           "⊔")
  ("\\top"            "⊤")
  ("\\bottom"         "⊥")
  ("\\vdash"          "⊢")
  ("\\dashv"          "⊣")
  ("\\Vdash"          "⊨")
  ("\\infty"          "∞")
  ("\\comp"           "∘")
  ("\\prf"            "↾")
  ("\\bind"           "≫=")
  ("\\mapsto"         "↦")
  ("\\hookrightarrow" "↪")
  ("\\uparrow"        "↑")

;; Iris specific
  ("\\fun"            "λ")
  ("\\mult"           "⋅")
  ("\\ent"            "⊢")
  ("\\valid"          "✓")
  ("\\diamond"        "◇")
  ("\\box"            "□")
  ("\\bbox"           "■")
  ("\\later"          "▷")
  ("\\pred"           "φ")
  ("\\and"            "∧")
  ("\\or"             "∨")
  ("\\comp"           "∘")
  ("\\ccomp"          "◎")
  ("\\all"            "∀")
  ("\\ex"             "∃")
  ("\\to"             "→")
  ("\\sep"            "∗")
  ("\\lc"             "⌜")
  ("\\rc"             "⌝")
  ("\\Lc"             "⎡")
  ("\\Rc"             "⎤")
  ("\\empty"          "∅")
  ("\\Lam"            "Λ")
  ("\\Sig"            "Σ")
  ("\\-"              "∖")
  ("\\aa"             "●")
  ("\\af"             "◯")
  ("\\auth"           "●")
  ("\\frag"           "◯")
  ("\\iff"            "↔")
  ("\\gname"          "γ")
  ("\\incl"           "≼")
  ("\\latert"         "▶")
  ("\\update"         "⇝")
  ("\\bind"           "≫=")

;; accents (for iLöb)
  ("\\\"o" "ö")

;; subscripts and superscripts
  ("^^+" "⁺") ("__+" "₊") ("^^-" "⁻")
  ("__0" "₀") ("__1" "₁") ("__2" "₂") ("__3" "₃") ("__4" "₄")
  ("__5" "₅") ("__6" "₆") ("__7" "₇") ("__8" "₈") ("__9" "₉")

  ("__a" "ₐ") ("__e" "ₑ") ("__h" "ₕ") ("__i" "ᵢ") ("__k" "ₖ")
  ("__l" "ₗ") ("__m" "ₘ") ("__n" "ₙ") ("__o" "ₒ") ("__p" "ₚ")
  ("__r" "ᵣ") ("__s" "ₛ") ("__t" "ₜ") ("__u" "ᵤ") ("__v" "ᵥ") ("__x" "ₓ")

;; Greek alphabet
  ("\\Alpha"  "Α")   ("\\alpha"  "α")
  ("\\Beta"   "Β")   ("\\beta"   "β")
  ("\\Gamma"  "Γ")   ("\\gamma"  "γ")
  ("\\Delta"  "Δ")   ("\\delta"  "δ")
  ("\\Epsilon"  "Ε") ("\\epsilon"  "ε")
  ("\\Zeta"   "Ζ")   ("\\zeta"   "ζ")
  ("\\Eta"  "Η")     ("\\eta"  "η")
  ("\\Theta"  "Θ")   ("\\theta"  "θ")
  ("\\Iota"   "Ι")   ("\\iota"   "ι")
  ("\\Kappa"  "Κ")   ("\\kappa"  "κ")
  ("\\Lamda"  "Λ")   ("\\lamda"  "λ")
  ("\\Lambda"   "Λ") ("\\lambda"   "λ")
  ("\\Mu"   "Μ")     ("\\mu"   "μ")
  ("\\Nu"   "Ν")     ("\\nu"   "ν")
  ("\\Xi"   "Ξ")     ("\\xi"   "ξ")
  ("\\Omicron"  "Ο") ("\\omicron"  "ο")
  ("\\Pi"   "Π")     ("\\pi"   "π")
  ("\\Rho"  "Ρ")     ("\\rho"  "ρ")
  ("\\Sigma"  "Σ")   ("\\sigma"  "σ")
  ("\\Tau"  "Τ")     ("\\tau"  "τ")
  ("\\Upsilon"  "Υ") ("\\upsilon"  "υ")
  ("\\Phi"  "Φ")     ("\\phi"  "φ")
  ("\\Chi"  "Χ")     ("\\chi"  "χ")
  ("\\Psi"  "Ψ")     ("\\psi"  "ψ")
  ("\\Omega"  "Ω")   ("\\omega"  "ω")
))
(state (init (trans)))
```

To use this input method, you should:

1. Enable the "Coq" input using your system settings or using the IBus
   configuration tool. The Coq input method typically appears in the category
   "other".
2. On some systems: In CoqIDE, you have to enable the input method by performing
   a right click on the text area, and selecting "System (IBus)" under "input
   method".

## CoqIDE 8.10+ Unicode input

Instead of configuring the input system-wide, you can use CoqIDE's support for
inputting Unicode symbols (introduced in Coq v8.10). To input a symbol, type a
LaTeX-like escape sequence, for example `\alpha` and then type
`<Shift>-<Space>`, which will expand it into `α`. Expansion will work on a
prefix of the command as well. You can also customize the expansion keyboard
shortcut, which is under Tools/LaTeX-to-unicode.

This system is configurable by adding a Unicode bindings file with additional
expansion sequences. On Linux this file should go in
`~/.config/coq/coqide.bindings` while on macOS it should go in
`~/Library/Application Support/Coq/coqide.bindings` (or under `$XDG_CONFIG_HOME`
if you have that set).

Here is a `coqide.bindings` file for a variety of symbols used in Iris:

```
# LaTeX-like sequences are natively supported (eg, \forall, \mapsto)
# Iris-specific abbreviations
\fun            λ
\mult           ⋅ 1
\ent            ⊢ 1
\valid          ✓
\diamond        ◇
\box            □ 1
\bbox           ■
\later          ▷
\pred           φ
\and            ∧
\or             ∨
\comp           ∘ 1
\ccomp          ◎
\all            ∀
\ex             ∃
\to             →
\sep            ∗
\lc             ⌜ 1
\rc             ⌝ 1
\Lc             ⎡ 1
\Rc             ⎤ 1
\lam            λ
\empty          ∅
\Lam            Λ
\Sig            Σ
\-              ∖ 1
\aa             ● 1
\af             ◯ 1
\auth           ●
\frag           ◯
\iff            ↔ 1
\gname          γ
\incl           ≼
\latert         ▶
\update         ⇝
# accents
\"o             ö
\Lob            Löb
# subscripts and superscripts
\^+             ⁺
\_+             ₊
\^-             ⁻
\_0             ₀
\_1             ₁
\_2             ₂
\_3             ₃
\_4             ₄
\_5             ₅
\_6             ₆
\_7             ₇
\_8             ₈
\_9             ₉
\_a             ₐ
\_e             ₑ
\_h             ₕ
\_i             ᵢ
\_k             ₖ
\_l             ₗ
\_m             ₘ
\_n             ₙ
\_o             ₒ
\_p             ₚ
\_r             ᵣ
\_s             ₛ
\_t             ₜ
\_u             ᵤ
\_v             ᵥ
\_x             ₓ
```
