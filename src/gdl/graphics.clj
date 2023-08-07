(ns gdl.graphics
  (:require [gdl.gdx :refer [graphics]]))

(defn screen-width  [] (.getWidth           graphics))
(defn screen-height [] (.getHeight          graphics))
(defn fps           [] (.getFramesPerSecond graphics))
