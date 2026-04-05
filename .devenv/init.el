;; Global config
(load-file (expand-file-name "~/.emacs"))


;; Project specific config

(load-file (let ((coding-system-for-read 'utf-8))
                (shell-command-to-string "agda --emacs-mode locate")))

(setq auto-mode-alist
   (append
     '(("\\.lagda.tree\\'" . agda2-mode)
       ("\\.lagda.md\\'" . agda2-mode)
       ("\\.lagda.org\\'" . agda2-mode))
     auto-mode-alist))
