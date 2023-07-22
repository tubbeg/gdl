; Main point : ! its an immutable animation, I can create once pass to hundred entities
; and they all update it itself.
(ns gdx.graphics.animation
  (:refer-clojure :exclude [update])
  (:require [gdx.graphics.image :as image]))

(defprotocol Animation
  (stopped?     [_])
  (restart      [_])
  (get-duration [_])
  (get-frame    [_]))

(defrecord ImmutableAnimation [frames frame-duration looping speed cnt maxcnt]
  Animation
  (stopped? [_]
    (and (not looping) (= cnt maxcnt)))
  (restart [this]
    (assoc this :cnt 0))
  (get-duration [_]
    maxcnt)
  (get-frame [this]
    ; int because cnt can be a float value
    (get frames (int (quot (dec cnt) frame-duration)))))

(defn update [{:keys [cnt speed maxcnt looping] :as this} delta]
  (let [newcnt (+ cnt (* speed delta))]
    (assoc this :cnt (cond (< newcnt maxcnt) newcnt
                           looping           (min maxcnt (- newcnt maxcnt))
                           :else             maxcnt))))

(def ^:private default-frame-duration 33)

(defn create
  [frames & {:keys [frame-duration looping]
             :or {frame-duration default-frame-duration}}]
  (map->ImmutableAnimation
    {:frames (vec frames)
     :frame-duration frame-duration
     :looping looping
     :speed 1
     :cnt 0
     :maxcnt (* (count frames) frame-duration)}))

; TODO just get-frame and render image there.... only used @ glittering
(defn draw-centered [animation position]
  (image/draw-centered (get-frame animation) position))
