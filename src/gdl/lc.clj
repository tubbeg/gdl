(ns gdl.lc
  "https://libgdx.com/wiki/app/the-life-cycle"
  (:require [x.x :refer [defsystem]]))

; TODO consistent last arg = context/game/state like in game.entity

(defsystem create  [_ state])
(defsystem dispose [_])

; screen/.*
(defsystem show   [_])
(defsystem hide   [_])
(defsystem render [_ state])
(defsystem tick   [_ state delta])
