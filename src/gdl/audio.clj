(ns gdl.audio
  (:require [gdl.assets :as assets]))

(defn play [file]
  (.play (assets/get-sound file)))
