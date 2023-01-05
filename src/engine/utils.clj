(ns engine.utils
  (:require [clojure.string :as str])
  (:import java.util.zip.ZipInputStream
           [com.badlogic.gdx Gdx]))

(defn set-var-root [v value]
  (alter-var-root v (constantly value)))

; http://stackoverflow.com/questions/1429172/list-files-inside-a-jar-file
(defn get-jar-entries [filter-predicate] ; TODO ?
  (let [src (.getCodeSource (.getProtectionDomain engine.GradientSprite))
        zip (ZipInputStream. (.openStream (.getLocation src)))]
    (loop [entry (.getNextEntry zip)
           hits []]
      (if entry
        (recur (.getNextEntry zip)
               (let [entryname (.getName entry)]
                 (if (filter-predicate entryname)
                   (conj hits entryname)
                   hits)))
        hits))))

(defn recursively-search-files [folder extensions]
  (loop [[file & remaining] (.list (.internal (Gdx/files) folder))
         result []]
    (cond (nil? file) result
          (.isDirectory file)
          (recur (concat remaining (.list file)) result)
          (extensions (.extension file))
          (recur remaining (conj result (str/replace (.path file) folder "")))
          :else
          (recur remaining result))))
