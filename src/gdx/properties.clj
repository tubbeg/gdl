(ns gdx.properties
  (:require [clojure.edn :as edn]
            [gdx.graphics :as g]))

; TODO schema assert (define in the edn file ?) -> can reuse @ editor ?
; => for all properties

; TODO assert distinct :id 's

; TODO just use sprite-idx directly.
(defn deserialize-image [{:keys [file sub-image-bounds]}]
  {:pre [file sub-image-bounds]}
  (let [[sprite-x sprite-y] (take 2 sub-image-bounds)
        [tilew tileh]       (drop 2 sub-image-bounds)]
    (g/get-sprite {:file file
                   :tilew tileh
                   :tileh tilew}
                  [(int (/ sprite-x tilew))
                   (int (/ sprite-y tileh))])))

(defn load-edn [file & {:keys [transform]}]
  (->> file
       (str "resources/") ; TODO (.internal (Gdx/files) folder)
       slurp
       edn/read-string
       (map #(if (:image %)
               (update % :image deserialize-image)
               %))
       (map (or transform identity))
       (#(zipmap (map :id %) %))))
