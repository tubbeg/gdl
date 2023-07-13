(ns gdx.audio
  (:require [gdx.asset-manager :as asset-manager]))

(defn play [filestring]
  (.play (asset-manager/file->sound filestring)))
