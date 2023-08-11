(ns gdl.lc
  "https://libgdx.com/wiki/app/the-life-cycle"
  (:require [x.x :refer [defsystem]]))

(defsystem create  [_])
(defsystem dispose [_])

; screen/.*
(defsystem show   [_])
(defsystem render [_])
(defsystem tick   [_ delta])
