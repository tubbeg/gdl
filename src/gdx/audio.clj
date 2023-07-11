(ns gdx.audio
  (:require [gdx.asset-manager :as asset-manager]))

; TODO type hint?
(defn play [filestring]
  (.play (asset-manager/file->sound filestring)))
