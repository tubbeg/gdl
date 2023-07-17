(ns gdx.audio
  (:require [gdx.assets :as assets]))

(defn play [file]
  (.play (assets/get-sound file)))
