Here we collect some information on how to set up your editor to properly input
and output the unicode characters used throughout Iris.

## General: Unicode Fonts

Most editors will just use system fonts for rendering unicode characters and do
not need furhter configuration once the fonts are installed.  Here are some
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
 ("\\mult"   ?⋅)
 ("\\ent"    ?⊢)
 ("\\valid"  ?✓)
 ("\\box"    ?□)
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
 ("\\lam"    ?λ)
 ("\\empty"  ?∅)
 ("\\Lam"    ?Λ)
 ("\\Sig"    ?Σ)
 ("\\-"      ?∖)
 ("\\aa"     ?●)
 ("\\af"     ?◯)
 ("\\iff"    ?↔)
 ("\\gname"  ?γ)
 ("\\incl"   ?≼)
 ("\\latert" ?▶)
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

## CoqIDE

CoqIDE does not have support for unicode itself, but you can use the Intelligent
Input Bus (IBus) framework for multilingual input. First, install `ibus-m17n`
via your system's package manager. Next, create a file `~/.m17n.d/coq.mim` to
configure an input method based on the math symbol list, and with some custom
aliases for symbols used a lot in Iris:

```
;; Usage: copy to ~/.m17n.d/coq.mim

(input-method t coq)
(description "Input method for Coq")
(title "Coq")

(map (trans

;; Standard math notations
  ("\\forall"         "∀")
  ("\\fun"            "λ")
  ("\\exists"         "∃")
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
  ("\\empty"          "∅")
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
  ("\\check"          "✓")
  ("\\later"          "▷")
  ("\\latert"         "▶")
  ("\\diamond"        "◇")
  ("\\square"         "□")
  ("\\bsquare"        "■")
  ("\\*"              "∗")
  ("\\included"       "≼")
  ("\\op"             "⋅")
  ("\\update"         "⇝")
  ("\\auth"           "●")
  ("\\frag"           "◯")
  ("\\lc"             "⌜")
  ("\\rc"             "⌝")
  ("\\Lc"             "⎡")
  ("\\Rc"             "⎤")

;; Commonly used sub- and superscripts
  ("^^+" ?⁺) ("__+" ?₊) ("^^-" ?⁻)
  ("__0" ?₀) ("__1" ?₁) ("__2" ?₂) ("__3" ?₃) ("__4" ?₄)
  ("__5" ?₅) ("__6" ?₆) ("__7" ?₇) ("__8" ?₈) ("__9" ?₉)

  ("__a" ?ₐ) ("__e" ?ₑ) ("__h" ?ₕ) ("__i" ?ᵢ) ("__k" ?ₖ)
  ("__l" ?ₗ) ("__m" ?ₘ) ("__n" ?ₙ) ("__o" ?ₒ) ("__p" ?ₚ)
  ("__r" ?ᵣ) ("__s" ?ₛ) ("__t" ?ₜ) ("__u" ?ᵤ) ("__v" ?ᵥ) ("__x" ?ₓ)

;; Commonly used acents
  ("\\\"o" "ö")

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
