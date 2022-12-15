from Fonctions.data.importData import *
from Fonctions.getters import *
from Fonctions.sorter import *
from Fonctions.checker import *
from Fonctions.setter import *

def listeBrancardierPossible(trajet) :
    br_possibles=[]
    for b in bra_data:
        #on récupère l'heure à laquelle le brancardier doit partir de son service actuelle pour rejoindre le service de provenance de la demande avant (ou  à) l'heure de départ de la demande
        heurePrevisionnelDepartLocalisation =getHeureDepartBrancardier(trajet, b)
        #si cette heure est comprise dans les horaires de disponibilité du bancardier :
        if  isHeureDepartDansHohaireBrancardier(heurePrevisionnelDepartLocalisation, b) :
            #si le brancardier est dispo pour cette heure : 
            if checkHeureDepartETHeureDispo(heurePrevisionnelDepartLocalisation,b):
                br_possibles.append(b)
    br_possibles.sort(key=takeTemps)
    return br_possibles

def affecterBrancardierTrajet(trajet):
     """
     Methode pour affecter un ou deux brancardier(s) à un trajet
     """  
     #on crée une liste contenant tous les brancardiers capable de réaliser le transport dans les temps
     br_possibles = listeBrancardierPossible(trajet)

     list_id = []
     list_noms = []
   
     if br_possibles==[]:
         if trajet["Nb Brancardiers"]=="1":
             list_id.append("None")
             list_noms.append("None")
             trajet["ID brancardiers"]=list_id
             trajet["Nom brancardiers"]=list_noms
             # trajet["Travail cumulé"]="None"
         if trajet["Nb Brancardiers"]=="2":
             list_id.append("None")
             list_noms.append("None")
             list_id.append("None")
             list_noms.append("None")
             trajet["ID brancardiers"]=list_id
             trajet["Nom brancardiers"]=list_noms
             # trajet["Travail cumulé"]="None"
     for b in bra_data: 
         if br_possibles==[]:
             return 0
         elif br_possibles[0]:
             if b==br_possibles[0]:
                 list_id.append(b["id"])
                 list_noms.append(b["nom"])
                 trajet["ID brancardiers"]=list_id
                 trajet["Nom brancardiers"]=list_noms
                 # trajet["Travail cumulé"]=b["travail_cumule"]
                 b["heure_dispo"]= trajet["Heure de RDV"] # on met a jour l'heure de dispo  du brancardier
                 b["localisation"]=trajet["ID service receveur"]
                 # print(b["travail_cumule"],"&",900)
                 b["travail_cumule"]=int(trajet["Temps moy"])+int(b["travail_cumule"])
     if trajet["Nb Brancardiers"]=="2":
         if len(br_possibles)==1:
             list_id.append("None")
             list_noms.append("None")
             trajet["ID brancardiers"]=list_id
             trajet["Nom brancardiers"]=list_noms
         if len(br_possibles)>=2:
             for b2 in bra_data:
                 if b2==br_possibles[1]:
                     list_id.append(b2["id"])
                     list_noms.append(b2["nom"])
                     trajet["ID brancardiers"]=list_id
                     trajet["Nom brancardiers"]=list_noms
                     # trajet["Travail cumulé"]=b2["travail_cumule"]
                     b2["heure_dispo"]= trajet["Heure de RDV"] # on met a jour l'heure de dispo  du brancardier
                     b2["localisation"]=trajet["ID service receveur"]
                     b2["travail_cumule"]=int(trajet["Temps moy"])+int(b2["travail_cumule"])
                     return br_possibles[0]

def retard(trajet):
    heure_depart = heure_to_intSecondes(trajet["heure_depart"])
    br_possible = listeBrancardierPossible(trajet)
    list_id = []
    list_nom = []
    retard = 0
    trajet["heure_depart_avant_retard"] = trajet["heure_depart"]
    while len(br_possible) <= int(trajet["Nb Brancardiers"]) :
        retard += 5
        heure_depart += 300
        trajet["heure_depart"] = intSecondes_to_heure(heure_depart)
        br_possible = listeBrancardierPossible(trajet)
    trajet["Retard"] = retard
    for b in bra_data :
        if b == br_possible[0] :
            list_id.append(b["id"])
            list_nom.append(b["nom"])
            b["heure_dispo"]= trajet["Heure de RDV"] # on met a jour l'heure de dispo  du brancardier
            b["localisation"]=trajet["ID service receveur"]
            b["travail_cumule"]=int(trajet["Temps moy"])+int(b["travail_cumule"])
        elif b == br_possible[1] :
            list_id.append(b["id"])
            list_nom.append(b["nom"])
            b["heure_dispo"]= trajet["Heure de RDV"] # on met a jour l'heure de dispo  du brancardier
            tps_manoeuvre = b["heure_dispo"]
            tps_manoeuvre = heure_to_intSecondes(tps_manoeuvre) + 120
            b["heure_dispo"] = intSecondes_to_heure(tps_manoeuvre)
            b["localisation"]=trajet["ID service receveur"]
            b["travail_cumule"]=int(trajet["Temps moy"])+int(b["travail_cumule"])
    trajet["ID brancardiers"] = list_id
    trajet["Nom brancardiers"] = list_nom

def affecterTrajetBrancardier():
    """
    Crée la liste des trajets effectués par chaque brancardier
    """
    for b in tot_bra_data :
        list_trajets=[]
        for t in tra_data :
            if t["Nb Brancardiers"]=="2":
                if b["ID"]==t["ID brancardiers"][0] or b["ID"]==t["ID brancardiers"][1]:
                    list_trajets.append(t["ID"])
            if t["Nb Brancardiers"]=="1":
                if b["ID"]==t["ID brancardiers"][0]:
                    list_trajets.append(t["ID"])
        b["Trajets"]=list_trajets
        b["Nombre de transports"]=len(list_trajets)

def triTrajets(listTrajets, tempsApresRdv, tempsAvantRdv):
    """
    Methode qui affecte un ordre à une liste de trajets en fonction de la valeur de la colonne "priorite" et selon un écart de temps défini, dans colonne 'ordre'
    """
    listTrajets.sort(key=takeDepart) #trie la liste en fonction de l'"heure depart"
    listeIDFinale=[]#liste qui va contenir la liste finale des id correspondants    
    #pour chaque trajet de la liste 
    for trajet in listTrajets:
        #on crée une liste qui va contenir les trajets dont les heure de départ sont proches
        listTrajetsProchedeTrajet=[]
        ##on crée une liste qui va contenir les id des trajets dont les heure de départ sont proches
        IDtrajetProche=[]      
        #on compare le trajet actuel (@trajet) avec les autres trajets (et lui-même)  
        for k in listTrajets :
            #on enregistre dans @delaiRDV la différence entre les heures de départ de @trajert avec un autre trajet  @k
                delaiRDV = heure_to_intSecondes(k["heure_depart"]) - heure_to_intSecondes(trajet["heure_depart"])
                #si @delaiRDV est compris dans les parametre [tempsAvantRdv] et[tempsApresRdv] 
                if delaiRDV<=tempsApresRdv and delaiRDV>=tempsAvantRdv:
                    #alors on ajoute le trajet à notre liste de trajets proches
                    listTrajetsProchedeTrajet.append(k)
        #on trie la liste de trajets proches par priorité
        listTrajetsProchedeTrajet.sort(key=takePriorite)
        #Pour chaque trajet proche
        for r in listTrajetsProchedeTrajet :
            #on ajoute l'id du trajet dans la liste d'id de trajets proches, rappel la liste que nous itérons est trié par priorité
            IDtrajetProche.append(r["ID"])
        #variable qui garde en mémoire le décalage pour insert au boin index dans la liste
        pasDecalage=0
        #on copie notre liste d'id de trajets proches, cette dernière va etre modifie par la suite d'ou sa duplication
        res_cop=IDtrajetProche.copy()
        #pour chaque element de la liste d'id (complète)
        for resElement in res_cop:
            #si l'element est déja présent dans notre liste finale
            if resElement in listeIDFinale :  
                #on récupère son index de la liste finale
                indexFin= listeIDFinale.index(resElement)
                #on récupère son index de la liste de trajet proche
                indexRes= IDtrajetProche.index(resElement)
                #pour déterminer la nouvelle position de l'élément dans la liste finale, on somme ses différents index avec le pas de décalage provoqué par l'ajout des éléments non présents
                position = indexFin+indexRes+pasDecalage
                #on retire l'élément de la liste finale                
                listeIDFinale.remove(resElement)
                #puis on le réinsere au bon index
                listeIDFinale.insert(position,resElement)
                #on retire l'element de la liste de trajet proche car il a été traité et ne doit plus etre pris compte dans les autres calculs
                IDtrajetProche.remove(resElement)
            #si l'élément n'est pas dans la liste finale
            else:
                #on l'ajoute a la fin de la liste finale
                listeIDFinale.append(resElement)
                #on ajoute un décalage correspondant à l'index du dernier élément ou la taille de la liste (pareil), ce décalage prend en compte l'ensemble des décalage provoqués              
                pasDecalage+=len(listeIDFinale)
    #notre liste d'id est maintenant triée comme nous le souhaitions, on va donc affecter l'ordre de passge selon nos regle de priorité
    #pour chaque id   
    for f in listeIDFinale :
        #on cherche le trajet @t qui a poour identifiant, l'id en cours @f
        for t in listTrajets :            
            if t["ID"]==f:
                #on affect à ce trajet son ordre de passage (correspond a l'index de @f dans la litse finale)
                t["ordre"]=listeIDFinale.index(f)
    return listTrajets

def exec(liste,tempsApresRdv, tempsAvantRdv):
    """
    Methode qui permet d'exécuter l'ensemble des autres fonctions pour un trajet, prioriser les trajets et les affectations 
    """
    for d in liste:
        #on défini les trajets retour
        isRetour(d)
        #on affecte le temps moyen du trajet selon la matrice de temps moyen 
        affecterTempsMoyen(d)
        #on détermine à partir de ce temps moyen, l'heure idéale pour partir du service de provenance afin d'arriver à l'heure de rdv dans le service de destination
        affecterHeureDepart(d)
        #on détermine à partir du service de destination et de l'ordre de priorité des services, la priorite concernant la réalisation de ce trajet
        affecterPriorite(d)
    # liste.sort(key=takeDepart)
    #on trie la nouvelle liste en fonction des priorité et de la "fenetre" de temps que l'on souhaite
    triTrajets(liste,tempsApresRdv,tempsAvantRdv)
    liste.sort(key=takeOrdre)

    #pour chaque trajet de la liste triée
    for d in liste:
        #on lui affecte un brancardier
        retard(d)
    recupTravailBrancardier()
    affecterTrajetBrancardier()
    exportALL()