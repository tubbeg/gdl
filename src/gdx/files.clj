(ns gdx.files
  (:require [clojure.string :as str]
            [gdx.app :as app])
  (:import [com.badlogic.gdx Gdx Files]
           [com.badlogic.gdx.files FileHandle]))

(app/defmanaged ^Files files Gdx/files)

; TODO files/get ?
(defn internal ^FileHandle [file]
  (.internal files file))

(defn ^:no-doc recursively-search-files [folder extensions]
  (loop [[^FileHandle file & remaining] (.list (internal folder))
         result []]
    (cond (nil? file) result
          (.isDirectory file)
          (recur (concat remaining (.list file)) result)
          (extensions (.extension file))
          (recur remaining (conj result (str/replace-first (.path file) folder "")))
          :else
          (recur remaining result))))
