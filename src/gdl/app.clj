(ns gdl.app
  (:require [x.x :refer [defcomponent]]
            [gdl.lc :as lc]
            [gdl.gdx :refer [app]])
  (:import (com.badlogic.gdx ScreenAdapter Game)))

(defn exit []
  (.exit app))

(defmacro with-context [& exprs]
  `(.postRunnable app (fn [] ~@exprs)))

(defprotocol Screen
  (show    [_])
  (render  [_])
  (tick    [_ delta]))

(defn- ->ScreenAdapter [screen]
  (proxy [ScreenAdapter] []
    (show []
      (show screen))
    (render [delta-seconds]
      (render screen)
      (let [delta-milliseconds (* delta-seconds 1000)]
        (tick screen delta-milliseconds)))))

; screens are map of keyword to screen
; for handling cyclic dependencies
; (options screen can set main screen and vice versa)
(declare ^:private screens)

(defn set-screen [k]
  (.setScreen ^Game (.getApplicationListener app)
              (k screens)))

(defn- map-vals [m f]
  (into {} (for [[k v] m] [k (f v)])))

(defcomponent *ns* screens
  (lc/create [_]
    (.bindRoot #'screens (map-vals screens ->ScreenAdapter))
    (set-screen (first (keys screens)))))
