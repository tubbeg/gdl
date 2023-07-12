(ns gdx.files
  (:require [clojure.string :as str]
            [gdx.app :as app])
  (:import [com.badlogic.gdx Gdx]))

(app/on-create
 ; tag
 (def files (Gdx/files)))

(defn internal [file]
  (.internal files file))

(defn ^:no-doc recursively-search-files [folder extensions]
  (loop [[file & remaining] (.list (internal folder))
         result []]
    (cond (nil? file) result
          (.isDirectory file)
          (recur (concat remaining (.list file)) result)
          (extensions (.extension file))
          (recur remaining (conj result (str/replace-first (.path file) folder "")))
          :else
          (recur remaining result))))
