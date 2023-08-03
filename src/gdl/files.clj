(ns gdl.files
  (:refer-clojure :exclude [get])
  (:require [clojure.string :as str]
            [gdl.utils :refer [set-var-root]])
  (:import [com.badlogic.gdx Gdx Files]
           [com.badlogic.gdx.files FileHandle]))

(declare ^:private ^Files files)

(defn load-state []
  (set-var-root #'files Gdx/files))

(defn get ^FileHandle [file] ; TODO keep internal?
  (.internal files file))

(defn ^:no-doc recursively-search-files [folder extensions]
  (loop [[^FileHandle file & remaining] (.list (get folder))
         result []]
    (cond (nil? file) result
          (.isDirectory file)
          (recur (concat remaining (.list file)) result)
          (extensions (.extension file))
          (recur remaining (conj result (str/replace-first (.path file) folder "")))
          :else
          (recur remaining result))))
