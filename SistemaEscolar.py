import csv
import hashlib
import hmac
import math
import re
import secrets
import time
from datetime import date
from decimal import Decimal, ROUND_HALF_UP
from bson.objectid import ObjectId
from pymongo import MongoClient, ReturnDocument
from pymongo.errors import PyMongoError
from dotenv import load_dotenv
import os

MONGO_URI = "mongodb://localhost:27017/"
NOME_BANCO = "escola"

# Regras da escola
BIMESTRES = 4
NOTA_APROVACAO = 7.0        # média a partir daqui: Aprovado
NOTA_RECUPERACAO = 5.0      # de 5 até 6,9: Recuperação; abaixo disso: Reprovado
LIMITE_FALTAS_PCT = 25      # passou de 25% de faltas (frequência < 75%): reprovado por falta
ATENCAO_FALTAS_PCT = 15     # passou de 15% de faltas (frequência < 85%): atenção
AULAS_PADRAO = 80

APROVADO = "Aprovado"
RECUPERACAO = "Recuperação"
REPROVADO_NOTA = "Reprovado por nota"
REPROVADO_FALTA = "Reprovado por falta"
ANDAMENTO = "Em andamento"
SEM_NOTAS = "Sem notas"
SITUACOES = [APROVADO, RECUPERACAO, REPROVADO_NOTA, REPROVADO_FALTA, ANDAMENTO, SEM_NOTAS]

VERSAO_LOGIN = 2
ALFABETO_CODIGO = "ABCDEFGHJKLMNPQRSTUVWXYZ23456789"
ITERACOES_SENHA = 200000
SENHA_MINIMA = 6
MAX_TENTATIVAS = 5
BLOQUEIO_SEGUNDOS = 30

RES_APROVADO = "Aprovado"
RES_EXAME = "Exame"
RES_REPROVADO = "Reprovado"
RES_ANDAMENTO = "Em andamento"
RESULTADOS = [RES_APROVADO, RES_EXAME, RES_REPROVADO, RES_ANDAMENTO]


# ----------------------------------------------
# FUNÇÕES SIMPLES (não usam o banco, só regras)
# ----------------------------------------------
def como_id(valor):
    """Aceita um ObjectId ou um texto e devolve sempre um ObjectId."""
    return valor if isinstance(valor, ObjectId) else ObjectId(str(valor))


def limpar_espacos(texto):
    """Engenharia de Software -> 'Engenharia de Software'."""
    return " ".join(str(texto).split())


def formatar_nota(valor):
    """7.5 -> '7,5'. None -> '-'. Arredonda como na escola (7,25 -> 7,3)."""
    if valor is None:
        return "-"
    d = Decimal(str(round(valor, 2))).quantize(Decimal("0.1"), rounding=ROUND_HALF_UP)
    return str(d).replace(".", ",")


def formatar_pct(valor):
    """92.5 -> '92,5%'. 100.0 -> '100%'. None -> '-'."""
    if valor is None:
        return "-"
    if float(valor).is_integer():
        return f"{int(valor)}%"
    return f"{valor:.1f}".replace(".", ",") + "%"


def media_de(valores):
    """Média dos números da lista, ignorando os None. Sem números -> None."""
    v = [x for x in valores if x is not None]
    return round(sum(v) / len(v), 2) if v else None


def _inteiro(texto):
    """12 -> 12. Qualquer outra coisa -> None."""
    texto = str(texto).strip()
    return int(texto) if texto.isascii() and texto.isdigit() else None


def ler_nota(texto, quem="A nota"):
    """Converte o texto digitado em nota de 0 a 10. Aceita vírgula."""
    texto = str(texto).strip().replace(",", ".")
    try:
        valor = float(texto)
    except ValueError:
        raise ValueError(f"{quem}: informe números, por exemplo 7,5.")
    if not math.isfinite(valor) or not (0 <= valor <= 10):
        raise ValueError(f"{quem} precisa estar entre 0 e 10.")
    return round(valor, 2)


def ler_bimestres(textos):
    """Converte os 4 campos de nota em uma lista [n1, n2, n3, n4]."""
    notas = []
    for i, texto in enumerate(textos, 1):
        if str(texto).strip() == "":
            notas.append(None)
        else:
            notas.append(ler_nota(texto, f"Nota do {i}º bimestre"))

    for i in range(1, len(notas)):
        if notas[i] is not None and notas[i - 1] is None:
            raise ValueError(f"Preencha os bimestres em ordem: o {i}º bimestre está vazio.")
    return notas


def ler_faltas(texto, aulas):
    """Faltas digitadas. Vazio vale 0. Não pode passar do total de aulas."""
    texto = str(texto).strip() or "0"
    faltas = _inteiro(texto)
    if faltas is None:
        raise ValueError("As faltas precisam ser um número inteiro, por exemplo 4.")
    if faltas > aulas:
        raise ValueError(f"As faltas não podem passar de {aulas} (total de aulas da disciplina).")
    return faltas


def ler_aulas(texto):
    """Total de aulas da disciplina no ano (1 a 500)."""
    aulas = _inteiro(texto)
    if aulas is None or not (1 <= aulas <= 500):
        raise ValueError("O total de aulas precisa ser um número de 1 a 500.")
    return aulas


def ler_aluno(nome, idade, email):
    """Confere os campos do aluno e devolve (nome, idade, email) limpos."""
    nome = limpar_espacos(nome)
    idade_n = _inteiro(idade)
    email = str(email).strip()
    if len(nome) < 3:
        raise ValueError("Informe o nome do aluno (mínimo 3 letras).")
    if idade_n is None or not (0 < idade_n <= 120):
        raise ValueError("Informe uma idade válida (1 a 120).")
    if email and not re.match(r"^[^@\s]+@[^@\s]+\.[^@\s]+$", email):
        raise ValueError("O e-mail parece inválido. Exemplo: ana@escola.com")
    return nome, idade_n, email


def faltas_maximas(aulas):
    """Quantas faltas o aluno pode ter sem reprovar por falta."""
    return aulas * LIMITE_FALTAS_PCT // 100


def frequencia(faltas, aulas):
    """Frequência em %: 80 aulas e 8 faltas -> 90.0."""
    return round((aulas - faltas) * 100 / aulas, 1)


def nivel_frequencia(faltas, aulas):
    """'critica', 'atencao' ou 'ok'."""
    if faltas * 100 > aulas * LIMITE_FALTAS_PCT:
        return "critica"
    if faltas * 100 > aulas * ATENCAO_FALTAS_PCT:
        return "atencao"
    return "ok"


def nota_necessaria(bimestres, alvo=NOTA_APROVACAO):
    """Que média o aluno precisa tirar nos bimestres que faltam para alcançar o alvo."""
    lancadas = [b for b in bimestres if b is not None]
    faltam = len(bimestres) - len(lancadas)
    if faltam == 0 or not lancadas:
        return None
    precisa = (alvo * len(bimestres) - sum(lancadas)) / faltam
    return max(0.0, math.ceil(round(precisa, 6) * 10) / 10)


def situacao_da_disciplina(bimestres, faltas, aulas):
    """A situação do aluno em UMA disciplina."""
    if nivel_frequencia(faltas, aulas) == "critica":
        return REPROVADO_FALTA
    lancadas = [b for b in bimestres if b is not None]
    if not lancadas:
        return SEM_NOTAS
    if len(lancadas) < len(bimestres):
        return ANDAMENTO
    media = media_de(lancadas)
    if media >= NOTA_APROVACAO:
        return APROVADO
    if media >= NOTA_RECUPERACAO:
        return RECUPERACAO
    return REPROVADO_NOTA


def dica_do_registro(r):
    """Frase de ajuda para o professor."""
    if r["nivel_freq"] == "critica":
        return "Passou do limite de faltas: reprovado por falta nesta disciplina."
    lancadas = [b for b in r["bimestres"] if b is not None]
    if not lancadas:
        return "Preencha os bimestres em ordem. Deixe em branco os que ainda não aconteceram."
    restam = BIMESTRES - len(lancadas)
    if restam == 0:
        return {
            APROVADO: "Aprovado: média 7 ou mais.",
            RECUPERACAO: "Recuperação: média entre 5 e 6,9.",
            REPROVADO_NOTA: "Reprovado por nota: média abaixo de 5."
        }.get(r["situacao"], "")
    if nota_necessaria(r["bimestres"], NOTA_RECUPERACAO) > 10:
        return "Mesmo com 10 nos bimestres que faltam, a média não chega a 5."
    p7 = nota_necessaria(r["bimestres"], NOTA_APROVACAO)
    if p7 <= 0:
        return "Aprovação garantida: nem com zero nos bimestres que faltam a média cai de 7."
    if p7 <= 10:
        return f"Para aprovar direto, precisa de média {formatar_nota(p7)} no(s) {restam} bimestre(s) que falta(m)."
    return "Não alcança média 7 nem tirando 10: dependerá da recuperação."


def alertas_do_registro(r):
    """Problemas de uma disciplina de um aluno."""
    res = []
    if r["nivel_freq"] == "critica":
        res.append((2, "Frequência",
                    f"Frequência {formatar_pct(r['freq'])}: {r['faltas']} faltas "
                    f"(máx. {r['faltas_max']}). Reprovado por falta."))
    elif r["nivel_freq"] == "atencao":
        res.append((1, "Frequência",
                    f"Frequência {formatar_pct(r['freq'])}: restam "
                    f"{r['faltas_max'] - r['faltas']} falta(s) até reprovar."))

    lancadas = [b for b in r["bimestres"] if b is not None]
    if not lancadas:
        return res
    media = media_de(lancadas)
    if len(lancadas) < BIMESTRES:
        restam = BIMESTRES - len(lancadas)
        p5 = nota_necessaria(r["bimestres"], NOTA_RECUPERACAO)
        p7 = nota_necessaria(r["bimestres"], NOTA_APROVACAO)
        if p5 > 10:
            res.append((1, "Nota", f"Média parcial {formatar_nota(media)}: nem com 10 chega a 7; só por recuperação."))
        elif media < NOTA_RECUPERACAO:
            res.append((1, "Nota", f"Média parcial {formatar_nota(media)}: precisa de {formatar_nota(p7)} nos {restam} bimestre(s) restantes."))
    elif media < NOTA_RECUPERACAO:
        res.append((2, "Nota", f"Reprovado por nota: média {formatar_nota(media)}."))
    elif media < NOTA_APROVACAO:
        res.append((1, "Nota", f"Em recuperação: média {formatar_nota(media)}."))
    return res


def resumo_do_boletim(linhas):
    """Números do cabeçalho do boletim de um aluno."""
    contagem = {s: 0 for s in SITUACOES}
    for r in linhas:
        contagem[r["situacao"]] += 1
    return {
        "media": media_de([r["media"] for r in linhas]),
        "freq": media_de([r["freq"] for r in linhas]) if linhas else None,
        "aprovadas": contagem[APROVADO],
        "reprovadas": contagem[REPROVADO_NOTA] + contagem[REPROVADO_FALTA],
        "recuperacao": contagem[RECUPERACAO],
        "baixa_freq": sum(1 for r in linhas if r["nivel_freq"] != "ok"),
        "total": len(linhas)
    }


# ----------------------------------------------
# LOGIN: SENHAS, MATRÍCULA E AUTENTICAÇÃO
# ----------------------------------------------
def criar_hash_senha(senha, sal=None):
    """Transforma a senha num texto irreversível."""
    sal = sal or secrets.token_hex(16)
    h = hashlib.pbkdf2_hmac("sha256", senha.encode("utf-8"), bytes.fromhex(sal), ITERACOES_SENHA)
    return f"pbkdf2${ITERACOES_SENHA}${sal}${h.hex()}"


def conferir_senha(senha, guardado):
    """True se a senha digitada gera o mesmo hash armazenado."""
    try:
        _tipo, voltas, sal, esperado = str(guardado).split("$")
        h = hashlib.pbkdf2_hmac("sha256", str(senha).encode("utf-8"), bytes.fromhex(sal), int(voltas))
    except (ValueError, TypeError):
        return False
    return hmac.compare_digest(h.hex(), esperado)


_HASH_FALSO = criar_hash_senha("senha-que-ninguem-usa")


def ler_senha(senha, confirmar=None):
    if len(senha) < SENHA_MINIMA:
        raise ValueError(f"A senha precisa ter pelo menos {SENHA_MINIMA} caracteres.")
    if confirmar is not None and senha != confirmar:
        raise ValueError("A confirmação não é igual à senha.")
    return senha


def ler_email_de_acesso(email):
    email = str(email).strip().lower()
    if not re.match(r"^[^@\s]+@[^@\s]+\.[^@\s]+$", email):
        raise ValueError("Informe um e-mail válido. Exemplo: prof@escola.com")
    return email


def normalizar_codigo(texto):
    return re.sub(r"[^A-Z0-9]", "", str(texto).upper())


def so_digitos(texto):
    return re.sub(r"\D", "", str(texto))


def resultado_da_situacao(situacao):
    if situacao == APROVADO:
        return RES_APROVADO
    if situacao == RECUPERACAO:
        return RES_EXAME
    if situacao in (REPROVADO_NOTA, REPROVADO_FALTA):
        return RES_REPROVADO
    return RES_ANDAMENTO


def resultado_geral(resultados):
    if not resultados:
        return "Sem disciplinas no boletim.", RES_ANDAMENTO
    rep = resultados.count(RES_REPROVADO)
    exa = resultados.count(RES_EXAME)
    if rep:
        return f"Reprovado em {rep} disciplina(s).", RES_REPROVADO
    if exa:
        return f"Exame em {exa} disciplina(s).", RES_EXAME
    if all(r == RES_APROVADO for r in resultados):
        return "Aprovado em todas as disciplinas.", RES_APROVADO
    return "Notas ainda em lançamento.", RES_ANDAMENTO


def _igual_sem_maiuscula(texto):
    return {"$regex": f"^{re.escape(texto)}$", "$options": "i"}


# ----------------------------------------------
# CLASSE QUE OPERA O MONGODB
# ----------------------------------------------
class Banco:
    def __init__(self, db):
        self.cursos = db["cursos"]
        self.disciplinas = db["disciplinas"]
        self.alunos = db["alunos"]
        self.matriculas = db["matriculas"]
        self.usuarios = db["usuarios"]
        self.contadores = db["contadores"]
        self.config = db["config"]
        self._falhas = {}

    def _bloqueado(self, chave):
        f = self._falhas.get(chave)
        if f and f[1] > time.monotonic():
            restam = int(f[1] - time.monotonic())
            raise ValueError(f"Muitas tentativas incorretas. Aguarde {restam} segundos.")

    def _errou(self, chave):
        f = self._falhas.setdefault(chave, [0, 0.0])
        if f[1] and f[1] <= time.monotonic():
            f[0], f[1] = 0, 0.0
        f[0] += 1
        if f[0] >= MAX_TENTATIVAS:
            f[0], f[1] = 0, time.monotonic() + BLOQUEIO_SEGUNDOS
        raise ValueError("Dados incorretos. Confira e tente de novo.")

    # ------------------ CURSOS ------------------
    def listar_cursos(self):
        lista = sorted(self.cursos.find({}), key=lambda c: c["nome"].casefold())
        for curso in lista:
            curso["qtd_disciplinas"] = self.disciplinas.count_documents({"curso_id": curso["_id"]})
            curso["qtd_alunos"] = self.alunos.count_documents({"curso_id": curso["_id"]})
        return lista

    def _conferir_curso(self, nome, id_atual=None):
        nome = limpar_espacos(nome)
        if len(nome) < 3:
            raise ValueError("Informe o nome do curso (mínimo 3 letras).")
        repetido = self.cursos.find_one({"nome": _igual_sem_maiuscula(nome)})
        if repetido and repetido["_id"] != id_atual:
            raise ValueError(f"Já existe um curso chamado '{nome}'.")
        return nome

    def criar_curso(self, nome):
        nome = self._conferir_curso(nome)
        self.cursos.insert_one({"nome": nome})
        return nome

    def atualizar_curso(self, curso_id, nome):
        curso_id = como_id(curso_id)
        nome = self._conferir_curso(nome, id_atual=curso_id)
        self.cursos.update_one({"_id": curso_id}, {"$set": {"nome": nome}})
        return nome

    def excluir_curso(self, curso_id):
        curso_id = como_id(curso_id)
        qtd = self.alunos.count_documents({"curso_id": curso_id})
        if qtd:
            raise ValueError(f"Este curso ainda tem {qtd} aluno(s). Exclua ou mude esses alunos de curso antes.")
        for disciplina in self.disciplinas.find({"curso_id": curso_id}):
            self.excluir_disciplina(disciplina["_id"])
        self.cursos.delete_one({"_id": curso_id})

    # ------------------ DISCIPLINAS ------------------
    def listar_disciplinas(self, curso_id=None):
        filtro = {}
        if curso_id is not None:
            filtro["curso_id"] = como_id(curso_id)
        nomes = {c["_id"]: c["nome"] for c in self.cursos.find({})}
        lista = list(self.disciplinas.find(filtro))
        for d in lista:
            d["curso_nome"] = nomes.get(d["curso_id"], "-")
            d["faltas_max"] = faltas_maximas(d["aulas"])
            d["qtd_alunos"] = self.matriculas.count_documents({"disciplina_id": d["_id"]})
        return sorted(lista, key=lambda d: (d["curso_nome"].casefold(), d["nome"].casefold()))

    def _conferir_disciplina(self, curso_id, nome, aulas, id_atual=None):
        nome = limpar_espacos(nome)
        if len(nome) < 2:
            raise ValueError("Informe o nome da disciplina.")
        aulas = ler_aulas(aulas)
        repetida = self.disciplinas.find_one({"curso_id": curso_id, "nome": _igual_sem_maiuscula(nome)})
        if repetida and repetida["_id"] != id_atual:
            raise ValueError(f"Este curso já tem a disciplina '{nome}'.")
        return nome, aulas

    def criar_disciplina(self, nome, curso_id, aulas):
        if not curso_id:
            raise ValueError("Escolha o curso da disciplina.")
        curso_id = como_id(curso_id)
        if self.cursos.find_one({"_id": curso_id}) is None:
            raise ValueError("Esse curso não existe mais.")
        nome, aulas = self._conferir_disciplina(curso_id, nome, aulas)
        self.disciplinas.insert_one({"nome": nome, "curso_id": curso_id, "aulas": aulas})
        for aluno in self.alunos.find({"curso_id": curso_id}):
            self._sincronizar_aluno(aluno["_id"])
        return nome

    def atualizar_disciplina(self, disciplina_id, nome, aulas):
        disciplina_id = como_id(disciplina_id)
        atual = self.disciplinas.find_one({"_id": disciplina_id})
        if atual is None:
            raise ValueError("Essa disciplina não existe mais.")
        nome, aulas = self._conferir_disciplina(atual["curso_id"], nome, aulas, id_atual=disciplina_id)
        maior = max([m["faltas"] for m in self.matriculas.find({"disciplina_id": disciplina_id})] or [0])
        if aulas < maior:
            raise ValueError(f"Há aluno com {maior} faltas: o total de aulas não pode ser menor que isso.")
        self.disciplinas.update_one({"_id": disciplina_id}, {"$set": {"nome": nome, "aulas": aulas}})
        return nome

    def excluir_disciplina(self, disciplina_id):
        disciplina_id = como_id(disciplina_id)
        self.matriculas.delete_many({"disciplina_id": disciplina_id})
        self.disciplinas.delete_one({"_id": disciplina_id})

    # ------------------ ALUNOS ------------------
    def listar_alunos(self, termo="", curso_id=None):
        filtro = {}
        termo = termo.strip()
        if termo:
            filtro["nome"] = {"$regex": re.escape(termo), "$options": "i"}
        if curso_id is not None:
            filtro["curso_id"] = como_id(curso_id)
        nomes = {c["_id"]: c["nome"] for c in self.cursos.find({})}
        lista = sorted(self.alunos.find(filtro), key=lambda a: a["nome"].casefold())
        for aluno in lista:
            aluno["curso_nome"] = nomes.get(aluno.get("curso_id"), "Sem curso")
        return lista

    def _curso_do_aluno(self, curso_id):
        if not curso_id:
            raise ValueError("Escolha o curso do aluno.")
        curso_id = como_id(curso_id)
        curso = self.cursos.find_one({"_id": curso_id})
        if curso is None:
            raise ValueError("Esse curso não existe mais.")
        qtd = self.disciplinas.count_documents({"curso_id": curso_id})
        if qtd == 0:
            raise ValueError(f"O curso '{curso['nome']}' ainda não tem disciplinas.")
        return curso_id, qtd

    def _nova_matricula(self):
        ano = date.today().year
        doc = self.contadores.find_one_and_update(
            {"_id": f"matricula-{ano}"}, {"$inc": {"n": 1}},
            upsert=True, return_document=ReturnDocument.AFTER)
        return f"{ano}{doc['n']:05d}"

    def criar_aluno_completo(self, nome, idade, email, curso_id, senha=""):
        nome, idade, email = ler_aluno(nome, idade, email)
        curso_id, qtd = self._curso_do_aluno(curso_id)
        if senha != "":
            ler_senha(senha)
        matricula = self._nova_matricula()
        senha_usada = senha or matricula
        aluno_id = self.alunos.insert_one({
            "nome": nome, "idade": idade, "email": email, "curso_id": curso_id,
            "matricula": matricula, "senha": criar_hash_senha(senha_usada)}).inserted_id
        self._sincronizar_aluno(aluno_id)
        return {"nome": nome, "qtd": qtd, "matricula": matricula,
                "senha": senha_usada, "senha_padrao": senha == ""}

    def criar_aluno(self, nome, idade, email, curso_id, senha=""):
        r = self.criar_aluno_completo(nome, idade, email, curso_id, senha)
        return r["nome"], r["qtd"]

    def atualizar_aluno(self, aluno_id, nome, idade, email, curso_id, nova_senha=""):
        aluno_id = como_id(aluno_id)
        nome, idade, email = ler_aluno(nome, idade, email)
        curso_id, _qtd = self._curso_do_aluno(curso_id)
        dados = {"nome": nome, "idade": idade, "email": email, "curso_id": curso_id}
        if nova_senha != "":
            dados["senha"] = criar_hash_senha(ler_senha(nova_senha))
        self.alunos.update_one({"_id": aluno_id}, {"$set": dados})
        self._sincronizar_aluno(aluno_id)
        return nome

    def excluir_aluno(self, aluno_id):
        aluno_id = como_id(aluno_id)
        self.matriculas.delete_many({"aluno_id": aluno_id})
        self.alunos.delete_one({"_id": aluno_id})

    def _sincronizar_aluno(self, aluno_id):
        aluno = self.alunos.find_one({"_id": aluno_id})
        if aluno is None:
            return
        do_curso = []
        if aluno.get("curso_id"):
            do_curso = [d["_id"] for d in self.disciplinas.find({"curso_id": aluno["curso_id"]})]
        existentes = set()
        for m in list(self.matriculas.find({"aluno_id": aluno_id})):
            if m["disciplina_id"] in do_curso and m["disciplina_id"] not in existentes:
                existentes.add(m["disciplina_id"])
            else:
                self.matriculas.delete_one({"_id": m["_id"]})
        for disciplina_id in do_curso:
            if disciplina_id not in existentes:
                self.matriculas.insert_one({
                    "aluno_id": aluno_id, "disciplina_id": disciplina_id,
                    "bimestres": [None] * BIMESTRES, "faltas": 0
                })

    # ------------------ NOTAS E FALTAS ------------------
    def _registro(self, m, disciplina):
        aulas = disciplina["aulas"]
        faltas = m["faltas"]
        bimestres = list(m["bimestres"])
        return {
            "matricula_id": m["_id"], "disciplina_id": disciplina["_id"],
            "disciplina": disciplina["nome"], "aulas": aulas, "faltas": faltas,
            "faltas_max": faltas_maximas(aulas), "bimestres": bimestres,
            "media": media_de(bimestres),
            "freq": frequencia(faltas, aulas),
            "nivel_freq": nivel_frequencia(faltas, aulas),
            "situacao": situacao_da_disciplina(bimestres, faltas, aulas)
        }

    def boletim(self, aluno_id):
        aluno_id = como_id(aluno_id)
        discs = {d["_id"]: d for d in self.disciplinas.find({})}
        linhas = [self._registro(m, discs[m["disciplina_id"]])
                  for m in self.matriculas.find({"aluno_id": aluno_id})
                  if m["disciplina_id"] in discs]
        return sorted(linhas, key=lambda r: r["disciplina"].casefold())

    def lancar(self, matricula_id, notas_texto, faltas_texto):
        m = self.matriculas.find_one({"_id": como_id(matricula_id)})
        if m is None:
            raise ValueError("Essa disciplina não está mais no boletim.")
        disciplina = self.disciplinas.find_one({"_id": m["disciplina_id"]})
        bimestres = ler_bimestres(notas_texto)
        faltas = ler_faltas(faltas_texto, disciplina["aulas"])
        self.matriculas.update_one({"_id": m["_id"]}, {"$set": {"bimestres": bimestres, "faltas": faltas}})
        return disciplina["nome"]

    # ------------------ USUÁRIOS E AUTENTICAÇÃO ------------------
    def tem_usuarios(self):
        return self.usuarios.count_documents({}) > 0

    def entrar_funcionario(self, email, senha):
        email = str(email).strip().lower()
        if not email or not senha:
            raise ValueError("Preencha o e-mail e a senha.")
        chave = f"func:{email}"
        self._bloqueado(chave)
        u = self.usuarios.find_one({"email": email})
        ok = conferir_senha(senha, u["senha"] if u else _HASH_FALSO)
        if u is None or not ok:
            self._errou(chave)
        self._falhas.pop(chave, None)
        return {"_id": u["_id"], "nome": u["nome"], "email": u["email"]}

    def entrar_aluno(self, matricula, senha):
        matricula = so_digitos(matricula)
        if not matricula or not senha:
            raise ValueError("Preencha a matrícula e a senha.")
        chave = f"aluno:{matricula}"
        self._bloqueado(chave)
        a = self.alunos.find_one({"matricula": matricula})
        ok = conferir_senha(senha, a.get("senha") if a else _HASH_FALSO)
        if a is None or not ok:
            self._errou(chave)
        self._falhas.pop(chave, None)
        return {"_id": a["_id"], "nome": a["nome"], "matricula": a["matricula"]}

    def criar_usuario(self, nome, email, senha, confirmar=None):
        nome = limpar_espacos(nome)
        if len(nome) < 3:
            raise ValueError("Informe o nome (mínimo 3 letras).")
        email = ler_email_de_acesso(email)
        ler_senha(senha, confirmar)
        if self.usuarios.find_one({"email": email}):
            raise ValueError("Já existe um acesso com esse e-mail.")
        self.usuarios.insert_one({"nome": nome, "email": email, "senha": criar_hash_senha(senha)})
        return nome

    def listar_usuarios(self):
        lista = [{"_id": u["_id"], "nome": u["nome"], "email": u["email"]} for u in self.usuarios.find({})]
        return sorted(lista, key=lambda u: u["nome"].casefold())

    def excluir_usuario(self, usuario_id, logado_id):
        usuario_id = como_id(usuario_id)
        if usuario_id == logado_id:
            raise ValueError("Você não pode excluir o seu próprio acesso.")
        self.usuarios.delete_one({"_id": usuario_id})

    def redefinir_senha_usuario(self, usuario_id, nova, confirmar=None):
        ler_senha(nova, confirmar)
        self.usuarios.update_one({"_id": como_id(usuario_id)}, {"$set": {"senha": criar_hash_senha(nova)}})

    def trocar_minha_senha(self, tipo, _id, atual, nova, confirmar):
        colecao = self.usuarios if tipo == "funcionario" else self.alunos
        doc = colecao.find_one({"_id": como_id(_id)})
        if doc is None or not conferir_senha(atual, doc.get("senha")):
            raise ValueError("A senha atual está incorreta.")
        ler_senha(nova, confirmar)
        colecao.update_one({"_id": doc["_id"]}, {"$set": {"senha": criar_hash_senha(nova)}})

    def criar_usuario_autorizado(self, admin_email, admin_senha, nome, email, senha, confirmar=None):
        self.entrar_funcionario(admin_email, admin_senha)
        return self.criar_usuario(nome, email, senha, confirmar)

    def redefinir_senha_por_email(self, email, nova, confirmar=None):
        email = str(email).strip().lower()
        ler_senha(nova, confirmar)
        u = self.usuarios.find_one({"email": email})
        if u is None:
            raise ValueError("Não existe acesso com esse e-mail.")
        self.usuarios.update_one({"_id": u["_id"]}, {"$set": {"senha": criar_hash_senha(nova)}})
        self._falhas.pop(f"func:{email}", None)
        return u["nome"]

    # -------------------- CÓDIGO DE RECUPERAÇÃO --------------------
    def tem_codigo_recuperacao(self):
        return self.config.find_one({"chave": "recuperacao"}) is not None

    def gerar_codigo_recuperacao(self):
        bruto = "".join(secrets.choice(ALFABETO_CODIGO) for _ in range(16))
        self.config.delete_many({"chave": "recuperacao"})
        self.config.insert_one({"chave": "recuperacao", "codigo": criar_hash_senha(bruto)})
        return "-".join(bruto[i:i + 4] for i in range(0, 16, 4))

    def redefinir_com_codigo(self, email, codigo, nova, confirmar=None):
        email = str(email).strip().lower()
        if not email or not str(codigo).strip():
            raise ValueError("Preencha o e-mail e o código de recuperação.")
        ler_senha(nova, confirmar)
        doc = self.config.find_one({"chave": "recuperacao"})
        if doc is None:
            raise ValueError("Ainda não existe código de recuperação.")
        chave = "recuperacao"
        self._bloqueado(chave)
        u = self.usuarios.find_one({"email": email})
        ok = conferir_senha(normalizar_codigo(codigo), doc["codigo"])
        if u is None or not ok:
            self._errou(chave)
        self._falhas.pop(chave, None)
        self._falhas.pop(f"func:{email}", None)
        self.usuarios.update_one({"_id": u["_id"]}, {"$set": {"senha": criar_hash_senha(nova)}})
        return self.gerar_codigo_recuperacao()

    def redefinir_senha_aluno(self, aluno_id, nova=""):
        aluno = self.alunos.find_one({"_id": como_id(aluno_id)})
        if aluno is None:
            raise ValueError("Aluno não encontrado.")
        if nova != "":
            ler_senha(nova)
            senha = nova
        else:
            senha = aluno.get("matricula")
            if not senha:
                raise ValueError("Este aluno ainda não tem matrícula.")
        self.alunos.update_one({"_id": aluno["_id"]}, {"$set": {"senha": criar_hash_senha(senha)}})
        self._falhas.pop(f"aluno:{aluno.get('matricula', '')}", None)
        return aluno["nome"], nova == ""

    def garantir_acessos(self):
        novos = 0
        for a in self.alunos.find({}):
            if not a.get("matricula"):
                m = self._nova_matricula()
                self.alunos.update_one({"_id": a["_id"]}, {"$set": {"matricula": m, "senha": criar_hash_senha(m)}})
                novos += 1
        return novos

    def visao_do_aluno(self, aluno_id):
        aluno = self.alunos.find_one({"_id": como_id(aluno_id)})
        if aluno is None:
            raise ValueError("Aluno não encontrado.")
        curso = self.cursos.find_one({"_id": aluno.get("curso_id")})
        linhas = [{"disciplina": r["disciplina"], "bimestres": r["bimestres"],
                   "media": r["media"],
                   "resultado": resultado_da_situacao(r["situacao"])}
                  for r in self.boletim(aluno["_id"])]
        return {"nome": aluno["nome"], "matricula": aluno.get("matricula", ""),
                "curso": curso["nome"] if curso else "Sem curso", "linhas": linhas,
                "geral": resultado_geral([l["resultado"] for l in linhas])}

    # -------------------- ANÁLISE --------------------
    def _todos_registros(self, curso_id=None):
        cursos = {c["_id"]: c["nome"] for c in self.cursos.find({})}
        discs = {d["_id"]: d for d in self.disciplinas.find({})}
        alunos = {a["_id"]: a for a in self.alunos.find({})}
        regs = []
        for m in self.matriculas.find({}):
            d = discs.get(m["disciplina_id"])
            a = alunos.get(m["aluno_id"])
            if d is None or a is None:
                continue
            if curso_id is not None and d["curso_id"] != curso_id:
                continue
            r = self._registro(m, d)
            r.update(aluno_id=a["_id"], aluno=a["nome"], curso=cursos.get(d["curso_id"], "-"))
            regs.append(r)
        return sorted(regs, key=lambda r: (r["aluno"].casefold(), r["disciplina"].casefold()))

    @staticmethod
    def _alertas(regs):
        alertas = []
        for r in regs:
            for gravidade, tipo, detalhe in alertas_do_registro(r):
                alertas.append({
                    "gravidade": gravidade,
                    "nivel": "Crítico" if gravidade == 2 else "Atenção",
                    "aluno_id": r["aluno_id"], "aluno": r["aluno"],
                    "curso": r["curso"], "disciplina_id": r["disciplina_id"],
                    "disciplina": r["disciplina"], "tipo": tipo, "detalhe": detalhe})
        return sorted(alertas, key=lambda a: (-a["gravidade"], a["aluno"].casefold(), a["disciplina"].casefold()))

    def analise(self, curso_id=None):
        curso_id = como_id(curso_id) if curso_id else None
        regs = self._todos_registros(curso_id)
        alertas = self._alertas(regs)

        filtro = {} if curso_id is None else {"curso_id": curso_id}
        situacoes = {s: 0 for s in SITUACOES}
        for r in regs:
            situacoes[r["situacao"]] += 1

        por_aluno = {}
        for r in regs:
            por_aluno.setdefault(r["aluno_id"], []).append(r)
        em_risco = []
        for aluno_id in {a["aluno_id"] for a in alertas}:
            seus = [a for a in alertas if a["aluno_id"] == aluno_id]
            regs_aluno = por_aluno[aluno_id]
            em_risco.append({
                "aluno": seus[0]["aluno"], "curso": seus[0]["curso"],
                "criticos": sum(1 for a in seus if a["gravidade"] == 2),
                "atencao": sum(1 for a in seus if a["gravidade"] == 1),
                "media": media_de([r["media"] for r in regs_aluno]),
                "freq_media": media_de([r["freq"] for r in regs_aluno])})
        em_risco.sort(key=lambda x: (-x["criticos"], -x["atencao"], x["aluno"].casefold()))

        ranking = []
        for d in self.listar_disciplinas(curso_id):
            rs = [r for r in regs if r["disciplina_id"] == d["_id"]]
            finais = [r for r in rs if r["situacao"] in (APROVADO, RECUPERACAO, REPROVADO_NOTA, REPROVADO_FALTA)]
            aprovados = sum(1 for r in finais if r["situacao"] == APROVADO)
            ranking.append({
                "disciplina": d["nome"], "curso": d["curso_nome"], "alunos": len(rs),
                "media": media_de([r["media"] for r in rs]),
                "freq_media": media_de([r["freq"] for r in rs]) if rs else None,
                "aprovacao": round(aprovados * 100 / len(finais), 1) if finais else None,
                "em_risco": len({a["aluno_id"] for a in alertas if a["disciplina_id"] == d["_id"]})})
        ranking.sort(key=lambda x: (x["media"] is None, x["media"] or 0, x["disciplina"].casefold()))

        resumo = {
            "alunos": self.alunos.count_documents(filtro),
            "cursos": 1 if curso_id else self.cursos.count_documents({}),
            "disciplinas": self.disciplinas.count_documents(filtro),
            "media_geral": media_de([r["media"] for r in regs]),
            "freq_media": media_de([r["freq"] for r in regs]) if regs else None,
            "em_risco": len(em_risco),
            "criticos": sum(1 for a in alertas if a["gravidade"] == 2),
            "atencao": sum(1 for a in alertas if a["gravidade"] == 1)}
        return {"resumo": resumo, "situacoes": situacoes, "alertas": alertas,
                "em_risco": em_risco, "disciplinas": ranking, "boletim": regs}


def exportar_csv(caminho, cabecalho, linhas):
    with open(caminho, "w", newline="", encoding="utf-8-sig") as arquivo:
        escritor = csv.writer(arquivo, delimiter=";")
        escritor.writerow(cabecalho)
        escritor.writerows(linhas)


def conectar(uri=MONGO_URI):
    try:
        cliente = MongoClient(uri, serverSelectionTimeoutMS=3000)
        cliente.admin.command("ping")
        banco = Banco(cliente[NOME_BANCO])
        banco.garantir_acessos()
        return banco
    except PyMongoError:
        return None

# -*- coding: utf-8 -*-
"""
Sistema Escolar - CustomTkinter + MongoDB
"""

import functools
import sys
from tkinter import ttk, messagebox, filedialog

import customtkinter as ctk
from pymongo.errors import PyMongoError

import banco as bd

if getattr(bd, "VERSAO_LOGIN", 0) < 2:
    sys.exit("O banco.py desta pasta é a versão ANTIGA.\n"
             "Substitua pelo banco.py novo.")

ctk.set_appearance_mode("dark")
ctk.set_default_color_theme("blue")

COR_DESTAQUE = "#1f6aa5"
COR_ALERTA = "#d98c1f"
COR_PERIGO = "#c0392b"
CORES_SITUACAO = {
    bd.APROVADO: "#2e9d6a", bd.RECUPERACAO: "#d98c1f",
    bd.REPROVADO_NOTA: "#e74c3c", bd.REPROVADO_FALTA: "#b83280",
    bd.ANDAMENTO: "#4a90d9", bd.SEM_NOTAS: "#8a8a8a"}
COR_ALUNO = "#2e9d6a"
CORES_RESULTADO = {bd.RES_APROVADO: "#2e9d6a", bd.RES_EXAME: "#d98c1f",
                   bd.RES_REPROVADO: "#e74c3c", bd.RES_ANDAMENTO: "#4a90d9"}
CORES_TAGS = dict(CORES_SITUACAO, g2="#e74c3c", g1="#d98c1f", **CORES_RESULTADO)


def aplicar_estilo_tabela():
    escuro = ctk.get_appearance_mode() == "Dark"
    fundo = "#1f1f1f" if escuro else "#ffffff"
    texto = "#e6e6e6" if escuro else "#1a1a1a"
    cabecalho = "#2d2d2d" if escuro else "#e6e6e6"

    estilo = ttk.Style()
    estilo.theme_use("clam")
    estilo.configure(
        "Treeview", background=fundo, fieldbackground=fundo,
        foreground=texto, borderwidth=0, rowheight=32, font=("Segoe UI", 12))
    estilo.configure(
        "Treeview.Heading", background=cabecalho, foreground=texto,
        relief="flat", font=("Segoe UI", 12, "bold"), padding=6)
    estilo.map("Treeview",
               background=[("selected", COR_DESTAQUE)],
               foreground=[("selected", "#ffffff")])
    estilo.map("Treeview.Heading", background=[("active", cabecalho)])


def seguro(silencioso=False):
    def decorador(funcao):
        @functools.wraps(funcao)
        def interno(self, *args, **kwargs):
            if self.app.banco is None:
                if not silencioso:
                    messagebox.showerror("Erro", "Sem conexão com o MongoDB.")
                return None
            try:
                return funcao(self, *args, **kwargs)
            except ValueError as erro:
                messagebox.showwarning("Atenção", str(erro))
            except PyMongoError as erro:
                messagebox.showerror("Erro no banco", f"Algo deu errado:\n{erro}")
            return None
        return interno
    return decorador


class Seletor(ctk.CTkComboBox):
    def __init__(self, master, vazio=None, **kwargs):
        super().__init__(master, state="readonly", values=[""], **kwargs)
        self.vazio = vazio
        self.mapa = {}

    def carregar(self, itens):
        escolhido = self.get()
        self.mapa = {}
        rotulos = []
        if self.vazio:
            self.mapa[self.vazio] = None
            rotulos.append(self.vazio)
        for rotulo, _id in itens:
            base, n = rotulo, 2
            while rotulo in self.mapa:
                rotulo = f"{base} #{n}"
                n += 1
            self.mapa[rotulo] = _id
            rotulos.append(rotulo)
        self.configure(values=rotulos or [""])
        self.set(escolhido if escolhido in self.mapa else (rotulos[0] if rotulos else ""))

    def valor(self):
        return self.mapa.get(self.get())

    def escolher(self, _id):
        for rotulo, valor in self.mapa.items():
            if valor == _id:
                self.set(rotulo)
                return
        self.set(self.vazio or "")


class Tabela(ctk.CTkFrame):
    def __init__(self, master, colunas, ao_selecionar=None):
        super().__init__(master, corner_radius=12)
        self.grid_columnconfigure(0, weight=1)
        self.grid_rowconfigure(0, weight=1)

        self.tv = ttk.Treeview(
            self, columns=[c[0] for c in colunas],
            show="headings", selectmode="browse")
        for chave, titulo, largura in colunas:
            self.tv.heading(chave, text=titulo)
            self.tv.column(chave, width=largura, anchor="w")
        self.tv.grid(row=0, column=0, sticky="nsew", padx=(10, 0), pady=10)

        barra = ctk.CTkScrollbar(self, command=self.tv.yview)
        barra.grid(row=0, column=1, sticky="ns", padx=(0, 6), pady=10)
        self.tv.configure(yscrollcommand=barra.set)

        for etiqueta, cor in CORES_TAGS.items():
            self.tv.tag_configure(etiqueta, foreground=cor)
        if ao_selecionar:
            self.tv.bind("<<TreeviewSelect>>", lambda _e: ao_selecionar())

    def preencher(self, linhas):
        for item in self.tv.get_children():
            self.tv.delete(item)
        for linha in linhas:
            etiquetas = (linha[2],) if len(linha) > 2 else ()
            self.tv.insert("", "end", iid=linha[0], values=linha[1], tags=etiquetas)

    def selecionado(self):
        selecao = self.tv.selection()
        return selecao[0] if selecao else None

    def desmarcar(self):
        self.tv.selection_remove(self.tv.selection())


def campo(form, texto, coluna, peso, criar, linha=0):
    form.grid_columnconfigure(coluna, weight=peso)
    ctk.CTkLabel(form, text=texto, anchor="w").grid(
        row=linha, column=coluna, sticky="w", padx=8, pady=(14, 0))
    widget = criar(form)
    widget.grid(row=linha + 1, column=coluna, sticky="ew", padx=8, pady=(4, 12))
    return widget


def botoes(form, definicoes, linha=2):
    barra = ctk.CTkFrame(form, fg_color="transparent")
    barra.grid(row=linha, column=0, columnspan=10, sticky="ew", padx=8, pady=(0, 14))
    lista = []
    for i, (texto, comando, cor) in enumerate(definicoes):
        barra.grid_columnconfigure(i, weight=1)
        extra = {}
        if cor == "neutro":
            extra = dict(fg_color=("gray70", "gray30"),
                         hover_color=("gray60", "gray40"),
                         text_color=("gray10", "gray90"))
        elif cor:
            extra = dict(fg_color=cor)
        botao = ctk.CTkButton(barra, text=texto, height=38, command=comando, **extra)
        botao.grid(row=0, column=i, sticky="ew", padx=4)
        lista.append(botao)
    return lista


def tag_do_alerta(gravidade):
    return "g2" if gravidade == 2 else "g1"


def fazer_cartoes(pai, linha, itens, tamanho=30):
    grade = ctk.CTkFrame(pai, fg_color="transparent")
    grade.grid(row=linha, column=0, sticky="ew", pady=(8, 0))
    valores = {}
    for i, (chave, texto) in enumerate(itens):
        grade.grid_columnconfigure(i, weight=1)
        card = ctk.CTkFrame(grade, corner_radius=12)
        card.grid(row=0, column=i, sticky="ew", padx=(0 if i == 0 else 8, 0))
        ctk.CTkLabel(card, text=texto, anchor="w",
                     text_color=("gray40", "gray60")).pack(
            anchor="w", padx=16, pady=(12, 0))
        rotulo = ctk.CTkLabel(card, text="-", anchor="w",
                              font=ctk.CTkFont(size=tamanho, weight="bold"))
        rotulo.pack(anchor="w", padx=16, pady=(0, 12))
        valores[chave] = rotulo
    return valores


class Pagina(ctk.CTkFrame):
    titulo = ""
    subtitulo = ""

    def __init__(self, app):
        super().__init__(app.area, fg_color="transparent")
        self.app = app
        self.grid_columnconfigure(0, weight=1)
        cab = ctk.CTkFrame(self, fg_color="transparent")
        cab.grid(row=0, column=0, sticky="ew", pady=(0, 8))
        ctk.CTkLabel(cab, text=self.titulo,
                     font=ctk.CTkFont(size=26, weight="bold")).grid(row=0, column=0, sticky="w")
        ctk.CTkLabel(cab, text=self.subtitulo, font=ctk.CTkFont(size=13),
                     text_color=("gray40", "gray60")).grid(row=1, column=0, sticky="w")
        self.lbl_aviso = ctk.CTkLabel(
            self, text="", anchor="w", justify="left", wraplength=800,
            text_color=COR_ALERTA, font=ctk.CTkFont(size=13, weight="bold"))
        self.lbl_aviso.grid(row=1, column=0, sticky="ew", pady=(0, 6))
        self.lbl_aviso.grid_remove()

    @property
    def banco(self):
        return self.app.banco

    def avisar(self, texto):
        self.lbl_aviso.configure(text=texto)
        if texto:
            self.lbl_aviso.grid()
        else:
            self.lbl_aviso.grid_remove()

    def cartoes(self, linha, itens, tamanho=30):
        return fazer_cartoes(self, linha, itens, tamanho)

    def ao_mostrar(self):
        pass


class PaginaInicio(Pagina):
    titulo = "Início"
    subtitulo = "Visão geral da escola"

    def __init__(self, app):
        super().__init__(app)
        self.grid_rowconfigure(3, weight=1)
        self.valores = self.cartoes(2, [
            ("alunos", "Alunos"), ("cursos", "Cursos"),
            ("disciplinas", "Disciplinas"), ("media_geral", "Média geral"),
            ("freq_media", "Frequência média")])

        baixo = ctk.CTkFrame(self, fg_color="transparent")
        baixo.grid(row=3, column=0, sticky="nsew", pady=(16, 0))
        baixo.grid_columnconfigure(0, weight=2)
        baixo.grid_columnconfigure(1, weight=3)
        baixo.grid_rowconfigure(0, weight=1)

        painel = ctk.CTkFrame(baixo, corner_radius=12)
        painel.grid(row=0, column=0, sticky="nsew", padx=(0, 10))
        painel.grid_columnconfigure(1, weight=1)
        ctk.CTkLabel(painel, text="Situação nas disciplinas", anchor="w",
                     font=ctk.CTkFont(size=15, weight="bold")).grid(
            row=0, column=0, columnspan=3, sticky="w", padx=16, pady=(14, 8))
        self.barras = {}
        for i, situacao in enumerate(bd.SITUACOES, 1):
            ctk.CTkLabel(painel, text=situacao, anchor="w",
                         text_color=CORES_SITUACAO[situacao]).grid(
                row=i, column=0, sticky="w", padx=(16, 8), pady=5)
            barra = ctk.CTkProgressBar(
                painel, progress_color=CORES_SITUACAO[situacao], height=12)
            barra.set(0)
            barra.grid(row=i, column=1, sticky="ew", padx=4)
            qtd = ctk.CTkLabel(painel, text="0", width=36, anchor="e")
            qtd.grid(row=i, column=2, padx=(4, 16))
            self.barras[situacao] = (barra, qtd)

        lado = ctk.CTkFrame(baixo, fg_color="transparent")
        lado.grid(row=0, column=1, sticky="nsew")
        lado.grid_columnconfigure(0, weight=1)
        lado.grid_rowconfigure(1, weight=1)
        ctk.CTkLabel(lado, text="Precisam de atenção (mais graves primeiro)", anchor="w",
                     font=ctk.CTkFont(size=15, weight="bold")).grid(
            row=0, column=0, sticky="w", pady=(2, 6))
        self.tabela = Tabela(lado, [("grav", "Gravidade", 85), ("aluno", "Aluno", 150),
                                    ("disc", "Disciplina", 140), ("det", "Detalhe", 330)])
        self.tabela.grid(row=1, column=0, sticky="nsew")

    @seguro(silencioso=True)
    def ao_mostrar(self):
        dados = self.banco.analise()
        resumo = dados["resumo"]
        for chave, rotulo in self.valores.items():
            valor = resumo[chave]
            if chave == "media_geral":
                texto = bd.formatar_nota(valor)
            elif chave == "freq_media":
                texto = bd.formatar_pct(valor)
            else:
                texto = str(valor)
            rotulo.configure(text=texto)

        total = sum(dados["situacoes"].values())
        for situacao, (barra, qtd) in self.barras.items():
            n = dados["situacoes"][situacao]
            barra.set(n / total if total else 0)
            qtd.configure(text=str(n))

        self.tabela.preencher([
            (str(i), (a["nivel"], a["aluno"], a["disciplina"], a["detalhe"]),
             tag_do_alerta(a["gravidade"]))
            for i, a in enumerate(dados["alertas"][:12])])

        if resumo["cursos"] == 0:
            self.avisar("Comece pelo menu: 1 Cursos, 2 Disciplinas, 3 Alunos e 4 Notas e faltas.")
        elif resumo["disciplinas"] == 0:
            self.avisar("Já existe curso. Agora cadastre as disciplinas dele na tela 2 Disciplinas.")
        elif resumo["alunos"] == 0:
            self.avisar("O curso já tem disciplinas. Agora cadastre os alunos na tela 3 Alunos.")
        else:
            self.avisar("")


class PaginaCursos(Pagina):
    titulo = "Cursos"
    subtitulo = "Passo 1: cadastre os cursos"

    def __init__(self, app):
        super().__init__(app)
        self.curso_id = None
        self.cache = {}
        self.grid_rowconfigure(3, weight=1)

        form = ctk.CTkFrame(self, corner_radius=12)
        form.grid(row=2, column=0, sticky="ew", pady=8)
        self.ent_nome = campo(form, "Nome do curso", 0, 1, lambda f: ctk.CTkEntry(
            f, placeholder_text="Ex.: Engenharia de Software", height=38))
        self.btn_cadastrar, self.btn_alterar, self.btn_excluir, _ = botoes(form, [
            ("Cadastrar", self.cadastrar, None),
            ("Alterar", self.alterar, COR_ALERTA),
            ("Excluir", self.excluir, COR_PERIGO),
            ("Limpar", self.limpar, "neutro")])
        self.definir_botoes(False)

        self.tabela = Tabela(self, [("nome", "Curso", 440), ("disc", "Disciplinas", 120),
                                    ("alunos", "Alunos", 100)], self.ao_selecionar)
        self.tabela.grid(row=3, column=0, sticky="nsew", pady=(0, 8))

    def definir_botoes(self, tem_selecao):
        estado = "normal" if tem_selecao else "disabled"
        self.btn_alterar.configure(state=estado)
        self.btn_excluir.configure(state=estado)

    @seguro(silencioso=True)
    def ao_mostrar(self):
        self.listar()

    def listar(self):
        cursos = self.banco.listar_cursos()
        self.cache = {str(c["_id"]): c for c in cursos}
        self.tabela.preencher([
            (str(c["_id"]), (c["nome"], c["qtd_disciplinas"], c["qtd_alunos"]))
            for c in cursos])
        self.app.status(f"{len(cursos)} curso(s) cadastrado(s).")

    def ao_selecionar(self):
        iid = self.tabela.selecionado()
        if iid is None or iid not in self.cache:
            return
        curso = self.cache[iid]
        self.curso_id = curso["_id"]
        self.ent_nome.delete(0, "end")
        self.ent_nome.insert(0, curso["nome"])
        self.definir_botoes(True)

    @seguro()
    def cadastrar(self):
        nome = self.banco.criar_curso(self.ent_nome.get())
        self.limpar()
        self.listar()
        self.app.status(f"Curso '{nome}' cadastrado.")

    @seguro()
    def alterar(self):
        if self.curso_id is None:
            raise ValueError("Selecione um curso na tabela.")
        nome = self.banco.atualizar_curso(self.curso_id, self.ent_nome.get())
        self.limpar()
        self.listar()
        self.app.status(f"Curso '{nome}' atualizado com sucesso.")

    @seguro()
    def excluir(self):
        if self.curso_id is None:
            raise ValueError("Selecione um curso na tabela.")
        nome = self.ent_nome.get().strip()
        if not messagebox.askyesno(
                "Confirmar exclusão",
                f"Excluir o curso '{nome}'?\nAs disciplinas dele também serão excluídas."):
            return
        self.banco.excluir_curso(self.curso_id)
        self.limpar()
        self.listar()
        self.app.status(f"Curso '{nome}' excluído.")

    def limpar(self):
        self.ent_nome.delete(0, "end")
        self.curso_id = None
        self.tabela.desmarcar()
        self.definir_botoes(False)
        self.ent_nome.focus()


class PaginaDisciplinas(Pagina):
    titulo = "Disciplinas"
    subtitulo = "Passo 2: cadastre as disciplinas de cada curso"

    def __init__(self, app):
        super().__init__(app)
        self.disciplina_id = None
        self.curso_original = None
        self.cache = {}
        self.grid_rowconfigure(4, weight=1)

        form = ctk.CTkFrame(self, corner_radius=12)
        form.grid(row=2, column=0, sticky="ew", pady=8)
        self.sel_curso = campo(form, "Curso", 0, 3, lambda f: Seletor(f, height=38))
        self.ent_nome = campo(form, "Disciplina", 1, 3, lambda f: ctk.CTkEntry(
            f, placeholder_text="Ex.: Algoritmos", height=38))
        self.ent_aulas = campo(form, "Aulas no ano", 2, 1, lambda f: ctk.CTkEntry(
            f, placeholder_text=str(bd.AULAS_PADRAO), height=38))
        self.ent_aulas.insert(0, str(bd.AULAS_PADRAO))
        self.btn_cadastrar, self.btn_alterar, self.btn_excluir, _ = botoes(form, [
            ("Cadastrar", self.cadastrar, None),
            ("Alterar", self.alterar, COR_ALERTA),
            ("Excluir", self.excluir, COR_PERIGO),
            ("Limpar", self.limpar, "neutro")])
        self.definir_botoes(False)

        self.sel_filtro = Seletor(self, vazio="Todos os cursos", height=38,
                                  command=lambda _v: self.listar())
        self.sel_filtro.grid(row=3, column=0, sticky="ew", pady=(0, 8))
        self.tabela = Tabela(self, [
            ("nome", "Disciplina", 260), ("curso", "Curso", 230), ("aulas", "Aulas", 70),
            ("max", "Máx. de faltas", 110), ("alunos", "Alunos", 80)], self.ao_selecionar)
        self.tabela.grid(row=4, column=0, sticky="nsew", pady=(0, 8))

    def definir_botoes(self, tem_selecao):
        estado = "normal" if tem_selecao else "disabled"
        self.btn_alterar.configure(state=estado)
        self.btn_excluir.configure(state=estado)

    @seguro(silencioso=True)
    def ao_mostrar(self):
        itens = [(c["nome"], c["_id"]) for c in self.banco.listar_cursos()]
        self.sel_curso.carregar(itens)
        self.sel_filtro.carregar(itens)
        self.avisar("" if itens else "Cadastre pelo menos um curso na tela 1 Cursos antes de criar disciplinas.")
        self.listar()

    @seguro(silencioso=True)
    def listar(self):
        disciplinas = self.banco.listar_disciplinas(self.sel_filtro.valor())
        self.cache = {str(d["_id"]): d for d in disciplinas}
        self.tabela.preencher([
            (str(d["_id"]), (d["nome"], d["curso_nome"], d["aulas"],
                             d["faltas_max"], d["qtd_alunos"])) for d in disciplinas])
        self.app.status(f"{len(disciplinas)} disciplina(s) encontrada(s).")

    def ao_selecionar(self):
        iid = self.tabela.selecionado()
        if iid is None or iid not in self.cache:
            return
        d = self.cache[iid]
        self.disciplina_id = d["_id"]
        self.curso_original = d["curso_id"]
        self.sel_curso.escolher(d["curso_id"])
        self.ent_nome.delete(0, "end")
        self.ent_nome.insert(0, d["nome"])
        self.ent_aulas.delete(0, "end")
        self.ent_aulas.insert(0, str(d["aulas"]))
        self.definir_botoes(True)

    @seguro()
    def cadastrar(self):
        nome = self.banco.criar_disciplina(
            self.ent_nome.get(), self.sel_curso.valor(), self.ent_aulas.get())
        curso = self.sel_curso.get()
        self.limpar()
        self.listar()
        self.app.status(f"Disciplina '{nome}' cadastrada em {curso}.")

    @seguro()
    def alterar(self):
        if self.disciplina_id is None:
            raise ValueError("Selecione uma disciplina na tabela.")
        if self.sel_curso.valor() != self.curso_original:
            raise ValueError("Uma disciplina não muda de curso. Exclua e cadastre de novo.")
        nome = self.banco.atualizar_disciplina(
            self.disciplina_id, self.ent_nome.get(), self.ent_aulas.get())
        self.limpar()
        self.listar()
        self.app.status(f"Disciplina '{nome}' atualizada com sucesso.")

    @seguro()
    def excluir(self):
        if self.disciplina_id is None:
            raise ValueError("Selecione uma disciplina na tabela.")
        nome = self.ent_nome.get().strip()
        if not messagebox.askyesno(
                "Confirmar exclusão",
                f"Excluir a disciplina '{nome}'?\nAs notas e faltas também serão apagadas."):
            return
        self.banco.excluir_disciplina(self.disciplina_id)
        self.limpar()
        self.listar()
        self.app.status(f"Disciplina '{nome}' excluída.")

    def limpar(self):
        self.ent_nome.delete(0, "end")
        self.ent_aulas.delete(0, "end")
        self.ent_aulas.insert(0, str(bd.AULAS_PADRAO))
        self.disciplina_id = None
        self.curso_original = None
        self.tabela.desmarcar()
        self.definir_botoes(False)
        self.ent_nome.focus()


class PaginaAlunos(Pagina):
    titulo = "Alunos"
    subtitulo = "Passo 3: matricule os alunos em um curso"

    def __init__(self, app):
        super().__init__(app)
        self.aluno_id = None
        self.curso_original = None
        self.cache = {}
        self.grid_rowconfigure(4, weight=1)

        form = ctk.CTkFrame(self, corner_radius=12)
        form.grid(row=2, column=0, sticky="ew", pady=8)
        self.ent_nome = campo(form, "Nome", 0, 4, lambda f: ctk.CTkEntry(
            f, placeholder_text="Nome completo", height=38))
        self.ent_idade = campo(form, "Idade", 1, 1, lambda f: ctk.CTkEntry(
            f, placeholder_text="Ex.: 18", height=38))
        self.ent_email = campo(form, "E-mail (opcional)", 2, 3, lambda f: ctk.CTkEntry(
            f, placeholder_text="aluno@escola.com", height=38))
        self.sel_curso = campo(form, "Curso", 3, 3, lambda f: Seletor(
            f, vazio="Escolha o curso", height=38))
        self.ent_matricula = campo(form, "Matrícula (gerada sozinha)", 0, 4,
                                   lambda f: ctk.CTkEntry(f, height=38), linha=2)
        self.ent_matricula.configure(state="disabled")
        self.ent_senha = campo(form, "Senha de acesso (vazio = matrícula)",
                               2, 3, lambda f: ctk.CTkEntry(
                f, placeholder_text="Novo: vazio = matrícula", show="•",
                height=38), linha=2)
        (self.btn_cadastrar, self.btn_alterar, self.btn_excluir,
         self.btn_redef, _) = botoes(form, [
            ("Cadastrar", self.cadastrar, None),
            ("Alterar", self.alterar, COR_ALERTA),
            ("Excluir", self.excluir, COR_PERIGO),
            ("Redefinir senha", self.redefinir_senha, "neutro"),
            ("Limpar", self.limpar, "neutro")], linha=4)
        self.definir_botoes(False)

        filtros = ctk.CTkFrame(self, fg_color="transparent")
        filtros.grid(row=3, column=0, sticky="ew", pady=(0, 8))
        filtros.grid_columnconfigure(0, weight=3)
        filtros.grid_columnconfigure(1, weight=1)
        self.ent_busca = ctk.CTkEntry(
            filtros, placeholder_text="Buscar aluno pelo nome...", height=38)
        self.ent_busca.grid(row=0, column=0, sticky="ew", padx=(0, 8))
        self.ent_busca.bind("<KeyRelease>", lambda _e: self.listar())

        self.sel_filtro = Seletor(filtros, vazio="Todos os cursos", height=38,
                                  command=lambda _v: self.listar())
        self.sel_filtro.grid(row=0, column=1, sticky="ew")

        self.tabela = Tabela(self, [
            ("nome", "Nome", 250), ("matricula", "Matrícula", 110),
            ("idade", "Idade", 60), ("email", "E-mail", 210),
            ("curso", "Curso", 200)], self.ao_selecionar)
        self.tabela.grid(row=4, column=0, sticky="nsew", pady=(0, 8))

    def definir_botoes(self, tem_selecao):
        estado = "normal" if tem_selecao else "disabled"
        self.btn_alterar.configure(state=estado)
        self.btn_excluir.configure(state=estado)
        self.btn_redef.configure(state=estado)

    @seguro(silencioso=True)
    def ao_mostrar(self):
        cursos = self.banco.listar_cursos()
        itens = [(c["nome"], c["_id"]) for c in cursos]
        self.sel_curso.carregar(itens)
        self.sel_filtro.carregar(itens)
        if not cursos:
            self.avisar("Antes dos alunos, cadastre um curso (1) e as disciplinas dele (2).")
        elif not any(c["qtd_disciplinas"] for c in cursos):
            self.avisar("Nenhum curso tem disciplinas ainda.")
        else:
            self.avisar("")
        self.listar()

    @seguro(silencioso=True)
    def listar(self):
        alunos = self.banco.listar_alunos(
            self.ent_busca.get(), curso_id=self.sel_filtro.valor())
        self.cache = {str(a["_id"]): a for a in alunos}
        self.tabela.preencher([
            (str(a["_id"]), (a["nome"], a.get("matricula", "-"), a["idade"],
                             a.get("email") or "-", a["curso_nome"]))
            for a in alunos])
        self.app.status(f"{len(alunos)} aluno(s) encontrado(s).")

    def ao_selecionar(self):
        iid = self.tabela.selecionado()
        if iid is None or iid not in self.cache:
            return
        aluno = self.cache[iid]
        self.aluno_id = aluno["_id"]
        self.curso_original = aluno.get("curso_id")
        for entrada, texto in ((self.ent_nome, aluno["nome"]),
                               (self.ent_idade, str(aluno["idade"])),
                               (self.ent_email, aluno.get("email", ""))):
            entrada.delete(0, "end")
            entrada.insert(0, texto)
        self.sel_curso.escolher(aluno.get("curso_id"))
        self.ent_senha.delete(0, "end")
        self.ent_matricula.configure(state="normal")
        self.ent_matricula.delete(0, "end")
        self.ent_matricula.insert(0, aluno.get("matricula", ""))
        self.ent_matricula.configure(state="disabled")
        self.definir_botoes(True)

    @seguro()
    def cadastrar(self):
        r = self.banco.criar_aluno_completo(
            self.ent_nome.get(), self.ent_idade.get(), self.ent_email.get(),
            self.sel_curso.valor(), self.ent_senha.get())
        curso = self.sel_curso.get()
        self.limpar()
        self.listar()
        self.app.status(f"Aluno '{r['nome']}' matriculado em {curso}.")
        quando = "igual à matrícula" if r["senha_padrao"] else "a que você digitou"
        messagebox.showinfo(
            "Acesso do aluno criado",
            f"{r['nome']}\n\nMatrícula: {r['matricula']}\n"
            f"Senha inicial: {quando}\n\n"
            "Passe esses dados ao aluno. Ele poderá trocar a senha depois de entrar.")

    @seguro()
    def alterar(self):
        if self.aluno_id is None:
            raise ValueError("Selecione um aluno na tabela.")
        trocou = self.sel_curso.valor() != self.curso_original
        if trocou and self.sel_curso.valor() is not None and not messagebox.askyesno(
                "Trocar de curso",
                "Trocar o aluno de curso apaga as notas e faltas dele no curso atual. Continuar?"):
            return
        nome = self.banco.atualizar_aluno(
            self.aluno_id, self.ent_nome.get(), self.ent_idade.get(),
            self.ent_email.get(), self.sel_curso.valor(), self.ent_senha.get())
        self.limpar()
        self.listar()
        self.app.status(f"Aluno '{nome}' atualizado com sucesso.")

    @seguro()
    def redefinir_senha(self):
        if self.aluno_id is None:
            raise ValueError("Selecione um aluno na tabela.")
        nome, padrao = self.banco.redefinir_senha_aluno(
            self.aluno_id, self.ent_senha.get())
        self.ent_senha.delete(0, "end")
        quando = "igual à matrícula" if padrao else "a que você digitou"
        messagebox.showinfo("Senha redefinida", f"{nome}\n\nNova senha: {quando}.")
        self.app.status(f"Senha de '{nome}' redefinida.")

    @seguro()
    def excluir(self):
        if self.aluno_id is None:
            raise ValueError("Selecione um aluno na tabela.")
        nome = self.ent_nome.get().strip()
        if not messagebox.askyesno(
                "Confirmar exclusão",
                f"Excluir o aluno '{nome}'?\nO boletim dele também será apagado."):
            return
        self.banco.excluir_aluno(self.aluno_id)
        self.limpar()
        self.listar()
        self.app.status(f"Aluno '{nome}' excluído.")

    def limpar(self):
        for entrada in (self.ent_nome, self.ent_idade, self.ent_email, self.ent_senha):
            entrada.delete(0, "end")
        self.ent_matricula.configure(state="normal")
        self.ent_matricula.delete(0, "end")
        self.ent_matricula.configure(state="disabled")
        self.sel_curso.escolher(None)
        self.aluno_id = None
        self.curso_original = None
        self.tabela.desmarcar()
        self.definir_botoes(False)
        self.ent_nome.focus()


class PaginaNotas(Pagina):
    titulo = "Notas e faltas"
    subtitulo = "Passo 4: lance as notas e faltas dos alunos"

    def __init__(self, app):
        super().__init__(app)
        self.matricula_id = None
        self.cache = {}
        self.grid_rowconfigure(3, weight=1)

        topo = ctk.CTkFrame(self, corner_radius=12)
        topo.grid(row=2, column=0, sticky="ew", pady=8)
        topo.grid_columnconfigure(0, weight=2)
        topo.grid_columnconfigure(1, weight=3)
        ctk.CTkLabel(topo, text="Curso", anchor="w").grid(
            row=0, column=0, sticky="w", padx=14, pady=(12, 0))
        ctk.CTkLabel(topo, text="Aluno", anchor="w").grid(
            row=0, column=1, sticky="w", padx=14, pady=(12, 0))
        self.sel_curso = Seletor(topo, vazio="Todos os cursos", height=36,
                                 command=lambda _v: self.trocar_curso())
        self.sel_curso.grid(row=1, column=0, sticky="ew", padx=14, pady=(4, 8))
        self.sel_aluno = Seletor(topo, height=36, command=lambda _v: self.listar())
        self.sel_aluno.grid(row=1, column=1, sticky="ew", padx=14, pady=(4, 8))
        self.lbl_resumo = ctk.CTkLabel(
            topo, text="", anchor="w", font=ctk.CTkFont(size=14, weight="bold"))
        self.lbl_resumo.grid(row=2, column=0, columnspan=2, sticky="w",
                             padx=14, pady=(0, 12))

        self.tabela = Tabela(self, [
            ("disc", "Disciplina", 200), ("b1", "1º", 50), ("b2", "2º", 50),
            ("b3", "3º", 50), ("b4", "4º", 50), ("media", "Média", 65),
            ("faltas", "Faltas", 70), ("freq", "Frequência", 120),
            ("sit", "Situação", 150)], self.ao_selecionar)
        self.tabela.grid(row=3, column=0, sticky="nsew", pady=(0, 8))

        form = ctk.CTkFrame(self, corner_radius=12)
        form.grid(row=4, column=0, sticky="ew", pady=(0, 8))
        self.lbl_disc = ctk.CTkLabel(
            form, text="Selecione uma disciplina na tabela para lançar notas e faltas.",
            anchor="w", font=ctk.CTkFont(size=14, weight="bold"))
        self.lbl_disc.grid(row=0, column=0, columnspan=10, sticky="w",
                           padx=14, pady=(12, 0))

        self.ent_bim = [
            campo(form, f"{i}º bimestre", i - 1, 1, lambda f: ctk.CTkEntry(
                f, placeholder_text="0 a 10", height=36), linha=1)
            for i in range(1, bd.BIMESTRES + 1)]
        self.ent_faltas = campo(form, "Faltas", bd.BIMESTRES, 1, lambda f: ctk.CTkEntry(
            f, placeholder_text="0", height=36), linha=1)
        self.btn_salvar, _ = botoes(form, [
            ("Salvar notas e faltas", self.salvar, None),
            ("Cancelar", self.limpar, "neutro")], linha=3)
        self.lbl_dica = ctk.CTkLabel(
            form, text="", anchor="w", justify="left", wraplength=780,
            text_color=("gray30", "gray70"))
        self.lbl_dica.grid(row=4, column=0, columnspan=10, sticky="w",
                           padx=14, pady=(0, 12))
        self.definir_botoes(False)

    def definir_botoes(self, tem_selecao):
        self.btn_salvar.configure(state="normal" if tem_selecao else "disabled")

    @seguro(silencioso=True)
    def ao_mostrar(self):
        cursos = self.banco.listar_cursos()
        self.sel_curso.carregar([(c["nome"], c["_id"]) for c in cursos])
        self.carregar_alunos()

    def trocar_curso(self):
        self.carregar_alunos()

    @seguro(silencioso=True)
    def carregar_alunos(self):
        alunos = self.banco.listar_alunos(curso_id=self.sel_curso.valor())
        self.sel_aluno.carregar(
            [(f"{a['nome']} ({a['curso_nome']})", a["_id"]) for a in alunos])
        self.listar()

    @seguro(silencioso=True)
    def listar(self):
        self.limpar()
        aluno_id = self.sel_aluno.valor()
        if aluno_id is None:
            self.cache = {}
            self.tabela.preencher([])
            self.lbl_resumo.configure(text="Escolha um aluno para ver o boletim.",
                                      text_color=("gray40", "gray60"))
            return
        linhas = self.banco.boletim(aluno_id)
        self.cache = {str(r["matricula_id"]): r for r in linhas}
        self.tabela.preencher([
            (str(r["matricula_id"]),
             (r["disciplina"], *[bd.formatar_nota(b) for b in r["bimestres"]],
              bd.formatar_nota(r["media"]), f"{r['faltas']}/{r['aulas']}",
              self.texto_frequencia(r), r["situacao"]),
             r["situacao"]) for r in linhas])

        resumo = bd.resumo_do_boletim(linhas)
        if resumo["reprovadas"]:
            cor = CORES_SITUACAO[bd.REPROVADO_NOTA]
        elif resumo["recuperacao"] or resumo["baixa_freq"]:
            cor = COR_ALERTA
        else:
            cor = CORES_SITUACAO[bd.APROVADO]
        self.lbl_resumo.configure(
            text=f"Média {bd.formatar_nota(resumo['media'])}    "
                 f"Frequência {bd.formatar_pct(resumo['freq'])}    "
                 f"{resumo['aprovadas']} aprovada(s)    "
                 f"{resumo['recuperacao']} em recuperação    "
                 f"{resumo['reprovadas']} reprovada(s)",
            text_color=cor)
        self.app.status(f"{len(linhas)} disciplina(s) no boletim deste aluno.")

    @staticmethod
    def texto_frequencia(r):
        texto = bd.formatar_pct(r["freq"])
        if r["nivel_freq"] == "critica":
            return texto + " (crítica)"
        if r["nivel_freq"] == "atencao":
            return texto + " (baixa)"
        return texto

    def ao_selecionar(self):
        iid = self.tabela.selecionado()
        if iid is None or iid not in self.cache:
            return
        r = self.cache[iid]
        self.matricula_id = r["matricula_id"]
        self.lbl_disc.configure(
            text=f"{r['disciplina']}    {r['aulas']} aulas    "
                 f"máximo de {r['faltas_max']} faltas")
        for entrada, nota in zip(self.ent_bim, r["bimestres"]):
            entrada.delete(0, "end")
            if nota is not None:
                entrada.insert(0, bd.formatar_nota(nota))

        self.ent_faltas.delete(0, "end")
        self.ent_faltas.insert(0, str(r["faltas"]))
        self.lbl_dica.configure(text=bd.dica_do_registro(r))
        self.definir_botoes(True)

    @seguro()
    def salvar(self):
        if self.matricula_id is None:
            raise ValueError("Selecione uma disciplina na tabela.")
        disciplina = self.banco.lancar(
            self.matricula_id, [e.get() for e in self.ent_bim], self.ent_faltas.get())
        self.listar()
        self.app.status(f"Notas e faltas de {disciplina} salvas com sucesso.")

    def limpar(self):
        for entrada in self.ent_bim:
            entrada.delete(0, "end")
        self.ent_faltas.delete(0, "end")
        self.matricula_id = None
        self.lbl_disc.configure(
            text="Selecione uma disciplina na tabela para lançar notas e faltas.")
        self.lbl_dica.configure(text="")
        self.tabela.desmarcar()
        self.definir_botoes(False)


class PaginaAnalise(Pagina):
    titulo = "Análise"
    subtitulo = "Passo 5: acompanhe dados gerais e relatórios"

    VISOES = ["Alertas", "Alunos em risco", "Disciplinas", "Boletim geral"]

    def __init__(self, app):
        super().__init__(app)
        self.dados = {}
        self.grid_rowconfigure(4, weight=1)
        self.valores = self.cartoes(2, [
            ("em_risco", "Alunos em risco"), ("criticos", "Alertas críticos"),
            ("freq_media", "Frequência média"), ("media_geral", "Média geral")],
            tamanho=26)

        barra = ctk.CTkFrame(self, fg_color="transparent")
        barra.grid(row=3, column=0, sticky="ew", pady=(12, 8))
        barra.grid_columnconfigure(0, weight=2)
        barra.grid_columnconfigure(1, weight=2)
        self.sel_curso = Seletor(barra, vazio="Todos os cursos", height=38,
                                 command=lambda _v: self.atualizar())
        self.sel_curso.grid(row=0, column=0, sticky="ew", padx=(0, 8))
        self.cmb_visao = ctk.CTkComboBox(
            barra, values=self.VISOES, state="readonly", height=38,
            command=lambda _v: self.trocar_visao())
        self.cmb_visao.set(self.VISOES[0])
        self.cmb_visao.grid(row=0, column=1, sticky="ew", padx=(0, 8))
        ctk.CTkButton(barra, text="Exportar CSV", height=38,
                      command=self.exportar).grid(row=0, column=2, sticky="e")

        self.cabecalhos = {
            "Alertas": ["Gravidade", "Aluno", "Curso", "Disciplina", "Detalhe"],
            "Alunos em risco": ["Aluno", "Curso", "Críticos", "Atenção", "Média", "Frequência"],
            "Disciplinas": ["Disciplina", "Curso", "Alunos", "Média", "Frequência", "Aprovação", "Em risco"],
            "Boletim geral": ["Aluno", "Curso", "Disciplina", "Média", "Faltas", "Frequência", "Situação"]
        }

        larguras = {
            "Alertas": [85, 150, 150, 150, 420],
            "Alunos em risco": [200, 180, 80, 80, 80, 110],
            "Disciplinas": [190, 170, 60, 70, 100, 90, 70],
            "Boletim geral": [170, 150, 150, 65, 70, 90, 140]
        }
        self.tabelas = {}
        for visao, cab in self.cabecalhos.items():
            colunas = [(f"c{i}", t, w) for i, (t, w) in enumerate(zip(cab, larguras[visao])) if w]
            tabela = Tabela(self, colunas)
            tabela.grid(row=4, column=0, sticky="nsew", pady=(0, 8))
            tabela.grid_remove()
            self.tabelas[visao] = tabela
        self.visao = self.VISOES[0]
        self.tabelas[self.visao].grid()

    @seguro(silencioso=True)
    def ao_mostrar(self):
        self.sel_curso.carregar([(c["nome"], c["_id"]) for c in self.banco.listar_cursos()])
        self.atualizar()

    @seguro(silencioso=True)
    def atualizar(self):
        dados = self.banco.analise(self.sel_curso.valor())
        resumo = dados["resumo"]
        self.valores["em_risco"].configure(text=str(resumo["em_risco"]))
        self.valores["criticos"].configure(text=str(resumo["criticos"]))
        self.valores["freq_media"].configure(text=bd.formatar_pct(resumo["freq_media"]))
        self.valores["media_geral"].configure(text=bd.formatar_nota(resumo["media_geral"]))

        pct, nota = bd.formatar_pct, bd.formatar_nota
        v = {
            "Alertas": [
                ([a["nivel"], a["aluno"], a["curso"], a["disciplina"], a["detalhe"]],
                 tag_do_alerta(a["gravidade"])) for a in dados["alertas"]],
            "Alunos em risco": [
                ([x["aluno"], x["curso"], x["criticos"], x["atencao"],
                  nota(x["media"]), pct(x["freq_media"])],
                 "g2" if x["criticos"] else "g1") for x in dados["em_risco"]],
            "Disciplinas": [
                ([d["disciplina"], d["curso"], d["alunos"], nota(d["media"]),
                  pct(d["freq_media"]), pct(d["aprovacao"]), d["em_risco"]],
                 "g2" if d["em_risco"] and d["media"] is not None and d["media"] < 5 else None)
                for d in dados["disciplinas"]],
            "Boletim geral": [
                ([r["aluno"], r["curso"], r["disciplina"], nota(r["media"]),
                  f"{r['faltas']}/{r['aulas']}", pct(r["freq"]), r["situacao"]],
                 r["situacao"]) for r in dados["boletim"]]
        }
        self.dados = v
        for visao, tabela in self.tabelas.items():
            tabela.preencher([
                (str(i), tuple(linha), *([tag] if tag else []))
                for i, (linha, tag) in enumerate(v[visao])])

        if not dados["boletim"]:
            self.avisar("Ainda não há alunos matriculados para analisar.")
        elif not dados["alertas"]:
            self.avisar("")
        else:
            self.avisar(f"{resumo['criticos']} alerta(s) crítico(s) e {resumo['atencao']} de atenção.")
        self.app.status(f"Análise atualizada: {len(v[self.visao])} linha(s) em '{self.visao}'.")

    def trocar_visao(self):
        self.tabelas[self.visao].grid_remove()
        self.visao = self.cmb_visao.get()
        self.tabelas[self.visao].grid()
        self.app.status(f"Mostrando: {self.visao}.")

    @seguro()
    def exportar(self):
        linhas = [linha for linha, _tag in self.dados.get(self.visao, [])]
        if not linhas:
            raise ValueError("Não há dados para exportar nesta visão.")
        caminho = filedialog.asksaveasfilename(
            title="Salvar análise", defaultextension=".csv",
            initialfile=f"analise_{self.visao.lower().replace(' ', '_')}.csv",
            filetypes=[("Planilha CSV", "*.csv")])
        if not caminho:
            return
        bd.exportar_csv(caminho, self.cabecalhos[self.visao], linhas)
        self.app.status(f"'{self.visao}' salvo em {caminho}")


class PaginaAcessos(Pagina):
    titulo = "Acessos"
    subtitulo = "Professores e administração"

    def __init__(self, app):
        super().__init__(app)
        self.usuario_id = None
        self.cache = {}
        self.grid_rowconfigure(3, weight=1)

        form = ctk.CTkFrame(self, corner_radius=12)
        form.grid(row=2, column=0, sticky="ew", pady=8)
        self.ent_nome = campo(form, "Nome", 0, 3, lambda f: ctk.CTkEntry(
            f, placeholder_text="Nome do professor", height=38))
        self.ent_email = campo(form, "E-mail de acesso", 1, 3, lambda f: ctk.CTkEntry(
            f, placeholder_text="prof@escola.com", height=38))
        self.ent_senha = campo(form, "Senha", 2, 2, lambda f: ctk.CTkEntry(
            f, placeholder_text="Mínimo 6 caracteres", show="•", height=38))
        self.ent_conf = campo(form, "Confirmar senha", 3, 2, lambda f: ctk.CTkEntry(
            f, show="•", height=38))
        self.btn_cadastrar, self.btn_redefinir, self.btn_excluir, *_ = botoes(form, [
            ("Cadastrar acesso", self.cadastrar, None),
            ("Redefinir senha", self.redefinir, COR_ALERTA),
            ("Excluir", self.excluir, COR_PERIGO),
            ("Código de recuperação", self.gerar_codigo, "neutro"),
            ("Limpar", self.limpar, "neutro")])
        self.definir_botoes(False)

        self.tabela = Tabela(self, [("nome", "Nome", 320), ("email", "E-mail", 360)],
                             self.ao_selecionar)
        self.tabela.grid(row=3, column=0, sticky="nsew", pady=(0, 8))

    def definir_botoes(self, tem_selecao):
        estado = "normal" if tem_selecao else "disabled"
        self.btn_redefinir.configure(state=estado)
        self.btn_excluir.configure(state=estado)

    @seguro(silencioso=True)
    def ao_mostrar(self):
        self.listar()

    @seguro(silencioso=True)
    def listar(self):
        usuarios = self.banco.listar_usuarios()
        self.cache = {str(u["_id"]): u for u in usuarios}
        self.tabela.preencher([(str(u["_id"]), (u["nome"], u["email"])) for u in usuarios])
        self.app.status(f"{len(usuarios)} acesso(s) de professores/administração.")

    def ao_selecionar(self):
        iid = self.tabela.selecionado()
        if iid is None or iid not in self.cache:
            return
        u = self.cache[iid]
        self.usuario_id = u["_id"]
        for entrada, texto in ((self.ent_nome, u["nome"]), (self.ent_email, u["email"])):
            entrada.delete(0, "end")
            entrada.insert(0, texto)
        self.ent_senha.delete(0, "end")
        self.ent_conf.delete(0, "end")
        self.definir_botoes(True)

    @seguro()
    def cadastrar(self):
        nome = self.banco.criar_usuario(
            self.ent_nome.get(), self.ent_email.get(),
            self.ent_senha.get(), self.ent_conf.get())
        self.limpar()
        self.listar()
        self.app.status(f"Acesso de '{nome}' criado.")

    @seguro()
    def redefinir(self):
        if self.usuario_id is None:
            raise ValueError("Selecione um acesso na tabela.")
        self.banco.redefinir_senha_usuario(
            self.usuario_id, self.ent_senha.get(), self.ent_conf.get())
        nome = self.ent_nome.get()
        self.limpar()
        self.app.status(f"Senha de '{nome}' redefinida.")

    @seguro()
    def gerar_codigo(self):
        if self.banco.tem_codigo_recuperacao():
            pergunta = "Já existe um código de recuperação. Gerar um novo invalida o anterior. Continuar?"
        else:
            pergunta = "Gerar o código de recuperação da escola agora?"
        if not messagebox.askyesno("Código de recuperação", pergunta):
            return
        DialogoCodigo(self.app, self.banco.gerar_codigo_recuperacao())

    @seguro()
    def excluir(self):
        if self.usuario_id is None:
            raise ValueError("Selecione um acesso na tabela.")
        nome = self.ent_nome.get().strip()
        if self.usuario_id == self.app.usuario["_id"]:
            raise ValueError("Você não pode excluir o seu próprio acesso.")
        if not messagebox.askyesno("Confirmar exclusão", f"Excluir o acesso de '{nome}'?"):
            return
        self.banco.excluir_usuario(self.usuario_id, self.app.usuario["_id"])
        self.limpar()
        self.listar()
        self.app.status(f"Acesso de '{nome}' excluído.")

    def limpar(self):
        for entrada in (self.ent_nome, self.ent_email, self.ent_senha, self.ent_conf):
            entrada.delete(0, "end")
        self.usuario_id = None
        self.tabela.desmarcar()
        self.definir_botoes(False)
        self.ent_nome.focus()


class DialogoSenha(ctk.CTkToplevel):
    def __init__(self, raiz, tipo, _id):
        super().__init__(raiz)
        self.raiz, self.tipo, self._id = raiz, tipo, _id
        self.title("Trocar senha")
        self.geometry("380x470")
        self.resizable(False, False)
        self.grid_columnconfigure(0, weight=1)
        ctk.CTkLabel(self, text="Trocar senha",
                     font=ctk.CTkFont(size=20, weight="bold")).grid(row=0, column=0, pady=(22, 4))
        self.ent_atual = self._linha(1, "Senha atual")
        self.ent_nova = self._linha(3, "Nova senha (mínimo 6 caracteres)")
        self.ent_conf = self._linha(5, "Confirmar nova senha")
        self.lbl_erro = ctk.CTkLabel(self, text="", text_color="#e74c3c",
                                     wraplength=320, font=ctk.CTkFont(size=12))
        self.lbl_erro.grid(row=7, column=0, pady=(4, 0))
        ctk.CTkButton(self, text="Salvar nova senha", height=40,
                      command=self.salvar).grid(row=8, column=0, padx=30, pady=(10, 6), sticky="ew")
        ctk.CTkButton(self, text="Cancelar", height=34, fg_color="transparent",
                      text_color=("gray10", "gray90"),
                      hover_color=("gray75", "gray25"),
                      command=self.destroy).grid(row=9, column=0, padx=30, sticky="ew")
        self.ent_atual.bind("<Return>", lambda _e: self.salvar())
        self.ent_nova.bind("<Return>", lambda _e: self.salvar())
        self.ent_conf.bind("<Return>", lambda _e: self.salvar())
        self.after(120, self._prender)

    def _prender(self):
        try:
            self.transient(self.raiz)
            self.grab_set()
            self.ent_atual.focus()
        except Exception:
            pass

    def _linha(self, linha, texto):
        ctk.CTkLabel(self, text=texto, anchor="w").grid(row=linha, column=0, sticky="w", padx=30, pady=(12, 0))
        entrada = ctk.CTkEntry(self, show="•", height=38)
        entrada.grid(row=linha + 1, column=0, sticky="ew", padx=30, pady=(4, 0))
        return entrada

    def salvar(self):
        try:
            self.raiz.banco.trocar_minha_senha(
                self.tipo, self._id, self.ent_atual.get(),
                self.ent_nova.get(), self.ent_conf.get())
        except ValueError as erro:
            self.lbl_erro.configure(text=str(erro))
            return
        except PyMongoError as erro:
            self.lbl_erro.configure(text=f"Erro no banco: {erro}")
            return
        self.destroy()
        messagebox.showinfo("Senha alterada", "Sua senha foi alterada com sucesso.")


class DialogoCampos(ctk.CTkToplevel):
    def __init__(self, raiz, titulo, intro, campos, botao, acao):
        super().__init__(raiz)
        self.raiz, self.acao = raiz, acao
        self.title(titulo)
        self.geometry(f"430x{190 + 74 * len(campos)}")
        self.resizable(False, False)
        self.grid_columnconfigure(0, weight=1)
        ctk.CTkLabel(self, text=titulo, font=ctk.CTkFont(size=20, weight="bold")).grid(row=0, column=0, pady=(20, 2))
        ctk.CTkLabel(self, text=intro, wraplength=370, justify="left",
                     text_color=("gray35", "gray65")).grid(row=1, column=0, padx=30)
        self.entradas = []
        for i, (rotulo, senha) in enumerate(campos):
            ctk.CTkLabel(self, text=rotulo, anchor="w").grid(row=2 + 2 * i, column=0, sticky="w", padx=30, pady=(10, 0))
            entrada = ctk.CTkEntry(self, show="•" if senha else "", height=36)
            entrada.grid(row=3 + 2 * i, column=0, sticky="ew", padx=30, pady=(3, 0))
            entrada.bind("<Return>", lambda _e: self.confirmar())
            self.entradas.append(entrada)
        n = len(campos)
        self.lbl_erro = ctk.CTkLabel(self, text="", text_color="#e74c3c", wraplength=370,
                                     justify="left", font=ctk.CTkFont(size=12))
        self.lbl_erro.grid(row=2 + 2 * n, column=0, padx=30, pady=(6, 0))
        ctk.CTkButton(self, text=botao, height=40, command=self.confirmar).grid(
            row=3 + 2 * n, column=0, padx=30, pady=(8, 4), sticky="ew")
        ctk.CTkButton(self, text="Cancelar", height=32, fg_color="transparent",
                      text_color=("gray10", "gray90"), hover_color=("gray75", "gray25"),
                      command=self.destroy).grid(row=4 + 2 * n, column=0, padx=30, sticky="ew")
        self.after(120, self._prender)

    def _prender(self):
        try:
            self.transient(self.raiz)
            self.grab_set()
            self.entradas[0].focus()
        except Exception:
            pass

    def confirmar(self):
        try:
            resultado = self.acao([e.get() for e in self.entradas])
        except ValueError as erro:
            self.lbl_erro.configure(text=str(erro))
            return
        except PyMongoError as erro:
            self.lbl_erro.configure(text=f"Erro no banco: {erro}")
            return
        self.destroy()
        if resultado and resultado[0] == "codigo":
            DialogoCodigo(self.raiz, resultado[1])
        elif resultado and resultado[0] == "info":
            messagebox.showinfo("Pronto", resultado[1])


class DialogoCodigo(ctk.CTkToplevel):
    def __init__(self, raiz, codigo, esperar=False):
        super().__init__(raiz)
        self.codigo = codigo
        self.title("Código de recuperação")
        self.geometry("460x330")
        self.resizable(False, False)
        self.grid_columnconfigure(0, weight=1)
        ctk.CTkLabel(self, text="Código de recuperação",
                     font=ctk.CTkFont(size=20, weight="bold")).grid(row=0, column=0, pady=(22, 4))
        ctk.CTkLabel(
            self, wraplength=390, justify="left", text_color=("gray35", "gray65"),
            text="Guarde este código em lugar seguro. Ele permite redefinir a senha de um acesso da equipe.").grid(
            row=1, column=0, padx=30)
        self.ent_codigo = ctk.CTkEntry(self, height=48, justify="center",
                                       font=ctk.CTkFont(family="Consolas", size=22, weight="bold"))
        self.ent_codigo.grid(row=2, column=0, sticky="ew", padx=40, pady=(18, 6))
        self.ent_codigo.insert(0, codigo)
        self.ent_codigo.configure(state="readonly")
        self.lbl_copiado = ctk.CTkLabel(self, text="", text_color="#2e9d6a")
        self.lbl_copiado.grid(row=3, column=0)
        ctk.CTkButton(self, text="Copiar código", height=38, fg_color=("gray70", "gray30"),
                      hover_color=("gray60", "gray40"), text_color=("gray10", "gray90"),
                      command=self.copiar).grid(row=4, column=0, padx=40, pady=(4, 6), sticky="ew")
        ctk.CTkButton(self, text="Já guardei o código", height=40,
                      command=self.destroy).grid(row=5, column=0, padx=40, sticky="ew")
        self.after(120, self._prender)
        if esperar:
            raiz.wait_window(self)

    def _prender(self):
        try:
            self.transient(self.master)
            self.grab_set()
        except Exception:
            pass

    def copiar(self):
        self.clipboard_clear()
        self.clipboard_append(self.codigo)
        self.lbl_copiado.configure(text="Copiado!")


def misturar(cor_a, cor_b, t):
    a = [int(cor_a[i:i + 2], 16) for i in (1, 3, 5)]
    b = [int(cor_b[i:i + 2], 16) for i in (1, 3, 5)]
    return "#%02x%02x%02x" % tuple(round(x + (y - x) * t) for x, y in zip(a, b))


class TelaLogin(ctk.CTkFrame):
    MODOS = {
        "funcionario": dict(
            titulo="Acesso da equipe", cor=COR_DESTAQUE,
            sub="Professores e administração escolar",
            rotulo="E-mail", dica="prof@escola.com",
            rodape=""),
        "aluno": dict(
            titulo="Área do aluno", cor=COR_ALUNO,
            sub="Consulte suas notas e o resultado final",
            rotulo="Matrícula", dica="Ex.: 202600001",
            rodape="Primeiro acesso? Sua senha inicial é a sua matrícula."),
    }

    def __init__(self, raiz):
        super().__init__(raiz, fg_color="transparent")
        self.app = raiz
        self.modo = "funcionario"
        self.cor = COR_DESTAQUE
        self.primeiro = False
        self.grid_columnconfigure(0, weight=1)
        self.grid_rowconfigure(0, weight=1)

        cartao = ctk.CTkFrame(self, corner_radius=18)
        cartao.grid(row=0, column=0)
        cartao.grid_columnconfigure(0, weight=1)
        self.faixa = ctk.CTkFrame(cartao, height=8, corner_radius=0, fg_color=self.cor)
        self.faixa.grid(row=0, column=0, sticky="ew")
        corpo = ctk.CTkFrame(cartao, fg_color="transparent")
        corpo.grid(row=1, column=0, padx=40, pady=(26, 30))
        corpo.grid_columnconfigure(0, weight=1)

        ctk.CTkLabel(corpo, text="Sistema Escolar",
                     font=ctk.CTkFont(size=26, weight="bold")).grid(row=0, column=0)
        abas = ctk.CTkFrame(corpo, fg_color="transparent")
        abas.grid(row=1, column=0, sticky="ew", pady=(18, 14))
        abas.grid_columnconfigure(0, weight=1)
        abas.grid_columnconfigure(1, weight=1)
        self.btn_func = ctk.CTkButton(
            abas, text="Professor / Administração", height=38,
            command=lambda: self.trocar_modo("funcionario"))
        self.btn_func.grid(row=0, column=0, sticky="ew", padx=(0, 4))
        self.btn_aluno = ctk.CTkButton(
            abas, text="Aluno", height=38,
            command=lambda: self.trocar_modo("aluno"))
        self.btn_aluno.grid(row=0, column=1, sticky="ew", padx=(4, 0))

        self.lbl_titulo = ctk.CTkLabel(corpo, text="", font=ctk.CTkFont(size=19, weight="bold"))
        self.lbl_titulo.grid(row=2, column=0, sticky="w")
        self.lbl_sub = ctk.CTkLabel(corpo, text="", anchor="w", text_color=("gray40", "gray60"))
        self.lbl_sub.grid(row=3, column=0, sticky="w", pady=(0, 6))

        self.bloco_nome, self.ent_nome = self._campo(corpo, 4, "Seu nome", False)
        self.bloco_usuario, self.ent_usuario = self._campo(corpo, 5, "E-mail", False)
        self.lbl_usuario = self.bloco_usuario.rotulo
        self.bloco_senha, self.ent_senha = self._campo(corpo, 6, "Senha", True)
        self.bloco_conf, self.ent_conf = self._campo(corpo, 7, "Confirmar senha", True)

        self.chk_ver = ctk.CTkCheckBox(corpo, text="Mostrar senha", command=self.mostrar_senha)
        self.chk_ver.grid(row=8, column=0, sticky="w", pady=(0, 4))
        self.lbl_erro = ctk.CTkLabel(corpo, text="", text_color="#e74c3c",
                                     wraplength=340, justify="left", anchor="w",
                                     font=ctk.CTkFont(size=13, weight="bold"))
        self.lbl_erro.grid(row=9, column=0, sticky="w", pady=(2, 4))
        self.btn_entrar = ctk.CTkButton(corpo, text="Entrar", height=44,
                                        font=ctk.CTkFont(size=15, weight="bold"),
                                        command=self.entrar)
        self.btn_entrar.grid(row=10, column=0, sticky="ew", pady=(4, 10))
        self.lbl_rodape = ctk.CTkLabel(corpo, text="", wraplength=340, justify="left",
                                       anchor="w", text_color=("gray40", "gray60"),
                                       font=ctk.CTkFont(size=12))
        self.lbl_rodape.grid(row=11, column=0, sticky="w")
        self.links = ctk.CTkFrame(corpo, fg_color="transparent")
        self.links.grid(row=12, column=0, sticky="ew", pady=(6, 0))
        self.links.grid_columnconfigure(0, weight=1)
        self.links.grid_columnconfigure(1, weight=1)
        estilo = dict(height=30, fg_color="transparent", hover_color=("gray85", "gray25"),
                      text_color=("gray20", "gray80"), font=ctk.CTkFont(size=12, underline=True))
        self.btn_esqueci = ctk.CTkButton(self.links, text="Esqueci minha senha", command=self.esqueci, **estilo)
        self.btn_esqueci.grid(row=0, column=0, sticky="ew")
        self.btn_novo = ctk.CTkButton(self.links, text="Criar outro acesso", command=self.novo_acesso, **estilo)
        self.btn_novo.grid(row=0, column=1, sticky="ew")

        for entrada in (self.ent_nome, self.ent_usuario, self.ent_senha, self.ent_conf):
            entrada.bind("<Return>", lambda _e: self.entrar())

        self.aplicar_modo()
        if self.app.banco is None:
            self.erro("Sem conexão com o MongoDB em localhost:27017.")

    @staticmethod
    def _campo(pai, linha, texto, senha):
        bloco = ctk.CTkFrame(pai, fg_color="transparent")
        bloco.grid(row=linha, column=0, sticky="ew")
        bloco.rotulo = ctk.CTkLabel(bloco, text=texto, anchor="w")
        bloco.rotulo.grid(row=0, column=0, sticky="w", pady=(10, 0))
        entrada = ctk.CTkEntry(bloco, width=340, height=40, show="•" if senha else "")
        entrada.grid(row=1, column=0, sticky="ew", pady=(4, 0))
        return bloco, entrada

    def trocar_modo(self, modo):
        if modo == self.modo:
            return
        antes = self.cor
        self.modo = modo
        self.erro("")
        self.ent_senha.delete(0, "end")
        self.ent_conf.delete(0, "end")
        self.aplicar_modo()
        self.animar(antes, self.MODOS[modo]["cor"], 0)

    def animar(self, de, para, passo, total=8):
        try:
            self.pintar(misturar(de, para, passo / total))
            if passo < total:
                self.after(20, lambda: self.animar(de, para, passo + 1, total))
        except Exception:
            pass

    def pintar(self, cor):
        self.cor = cor
        escura = misturar(cor, "#000000", 0.2)
        self.faixa.configure(fg_color=cor)
        self.btn_entrar.configure(fg_color=cor, hover_color=escura)
        ativo, inativo = (self.btn_func, self.btn_aluno) if self.modo == "funcionario" else (self.btn_aluno, self.btn_func)
        ativo.configure(fg_color=cor, hover_color=escura, text_color="white")
        inativo.configure(fg_color=("gray78", "gray28"), hover_color=("gray70", "gray34"), text_color=("gray10", "gray90"))

    def aplicar_modo(self):
        m = self.MODOS[self.modo]
        self.primeiro = False
        if self.modo == "funcionario" and self.app.banco is not None:
            try:
                self.primeiro = not self.app.banco.tem_usuarios()
            except PyMongoError:
                self.primeiro = False
        self.lbl_titulo.configure(text="Primeiro acesso" if self.primeiro else m["titulo"])
        self.lbl_sub.configure(text="Ainda não há ninguém cadastrado. Crie o administrador do sistema." if self.primeiro else m["sub"])
        self.lbl_usuario.configure(text=m["rotulo"])
        self.ent_usuario.configure(placeholder_text=m["dica"])
        self.lbl_rodape.configure(text="" if self.primeiro else m["rodape"])
        self.btn_entrar.configure(text="Criar acesso e entrar" if self.primeiro else "Entrar")
        if self.primeiro:
            self.bloco_nome.grid()
            self.bloco_conf.grid()
            self.links.grid_remove()
        else:
            self.bloco_nome.grid_remove()
            self.bloco_conf.grid_remove()
            self.links.grid()
            if self.modo == "funcionario":
                self.btn_novo.grid()
            else:
                self.btn_novo.grid_remove()
        self.pintar(self.cor)
        self.ent_usuario.focus()

    def mostrar_senha(self):
        simbolo = "" if self.chk_ver.get() else "•"
        self.ent_senha.configure(show=simbolo)
        self.ent_conf.configure(show=simbolo)

    def erro(self, texto):
        self.lbl_erro.configure(text=texto)

    def esqueci(self):
        banco = self.app.banco
        if self.modo == "aluno":
            messagebox.showinfo("Esqueci minha senha", "Procure a secretaria da escola.")
            return
        if banco is None:
            self.erro("Sem conexão com o MongoDB.")
            return

        def acao(v):
            novo = banco.redefinir_com_codigo(v[0], v[1], v[2], v[3])
            return ("codigo", novo)

        DialogoCampos(
            self.app, "Esqueci minha senha", "Digite suas informações de recuperação.",
            [("E-mail do acesso", False), ("Código de recuperação", False),
             ("Nova senha (mínimo 6)", True), ("Confirmar senha", True)],
            "Redefinir senha", acao)

    def novo_acesso(self):
        banco = self.app.banco
        if banco is None:
            self.erro("Sem conexão com o MongoDB.")
            return

        def acao(v):
            nome = banco.criar_usuario_autorizado(v[0], v[1], v[2], v[3], v[4], v[5])
            return ("info", f"Acesso de '{nome}' criado.")

        DialogoCampos(
            self.app, "Criar outro acesso", "Insira as credenciais de quem autoriza e as do novo usuário.",
            [("E-mail autorizador", False), ("Senha autorizador", True),
             ("Nome novo acesso", False), ("E-mail novo acesso", False),
             ("Senha novo acesso", True), ("Confirmar senha", True)],
            "Criar acesso", acao)

    def entrar(self):
        banco = self.app.banco
        if banco is None:
            self.erro("Sem conexão com o MongoDB.")
            return
        try:
            if self.modo == "funcionario":
                codigo = None
                if self.primeiro:
                    banco.criar_usuario(self.ent_nome.get(), self.ent_usuario.get(),
                                        self.ent_senha.get(), self.ent_conf.get())
                    codigo = banco.gerar_codigo_recuperacao()
                usuario = banco.entrar_funcionario(self.ent_usuario.get(), self.ent_senha.get())
                if codigo:
                    DialogoCodigo(self.app, codigo, esperar=True)
                self.app.abrir_painel_escola(usuario)
            else:
                aluno = banco.entrar_aluno(self.ent_usuario.get(), self.ent_senha.get())
                self.app.abrir_painel_aluno(aluno)
        except ValueError as erro:
            self.erro(str(erro))
            if self.primeiro:
                self.ent_conf.delete(0, "end")
                self.ent_conf.focus()
            else:
                self.ent_senha.delete(0, "end")
                self.ent_senha.focus()
        except PyMongoError as erro:
            self.erro(f"Erro no banco de dados: {erro}")


class PainelEscola(ctk.CTkFrame):
    MENU = [("Início", ""), ("Cursos", "1"), ("Disciplinas", "2"),
            ("Alunos", "3"), ("Notas e faltas", "4"), ("Análise", "5"),
            ("Acessos", "6")]

    def __init__(self, raiz, usuario):
        super().__init__(raiz, fg_color="transparent")
        self.raiz = raiz
        self.usuario = usuario
        self.banco = raiz.banco
        self.grid_columnconfigure(1, weight=1)
        self.grid_rowconfigure(0, weight=1)

        self.criar_menu()
        self.area = ctk.CTkFrame(self, fg_color="transparent")
        self.area.grid(row=0, column=1, sticky="nsew", padx=(24, 24), pady=(20, 0))
        self.area.grid_columnconfigure(0, weight=1)
        self.area.grid_rowconfigure(0, weight=1)
        self.lbl_status = ctk.CTkLabel(self, text="", anchor="w", font=ctk.CTkFont(size=12))
        self.lbl_status.grid(row=1, column=1, sticky="ew", padx=28, pady=(4, 12))

        self.paginas = {
            "Início": PaginaInicio(self), "Cursos": PaginaCursos(self),
            "Disciplinas": PaginaDisciplinas(self), "Alunos": PaginaAlunos(self),
            "Notas e faltas": PaginaNotas(self), "Análise": PaginaAnalise(self),
            "Acessos": PaginaAcessos(self)}
        self.mostrar("Início")

    def criar_menu(self):
        menu = ctk.CTkFrame(self, width=220, corner_radius=0)
        menu.grid(row=0, column=0, rowspan=2, sticky="nsew")
        menu.grid_rowconfigure(10, weight=1)
        ctk.CTkLabel(menu, text="Sistema\nEscolar", justify="left",
                     font=ctk.CTkFont(size=22, weight="bold")).grid(
            row=0, column=0, sticky="w", padx=22, pady=(26, 22))

        self.botoes_menu = {}
        for i, (nome, passo) in enumerate(self.MENU, 1):
            botao = ctk.CTkButton(
                menu, text=f"{passo}    {nome}" if passo else nome, anchor="w",
                height=40, fg_color="transparent",
                text_color=("gray10", "gray90"), hover_color=("gray75", "gray25"),
                command=lambda n=nome: self.mostrar(n))
            botao.grid(row=i, column=0, sticky="ew", padx=14, pady=3)
            self.botoes_menu[nome] = botao

        self.lbl_usuario = ctk.CTkLabel(
            menu, text=f"{self.usuario['nome']}\n{self.usuario['email']}",
            justify="left", anchor="w", wraplength=180,
            text_color=("gray40", "gray60"), font=ctk.CTkFont(size=12))
        self.lbl_usuario.grid(row=11, column=0, sticky="w", padx=22, pady=(0, 6))
        self.btn_senha = ctk.CTkButton(
            menu, text="Trocar minha senha", height=32, anchor="w",
            fg_color="transparent", text_color=("gray10", "gray90"),
            hover_color=("gray75", "gray25"), command=self.trocar_senha)
        self.btn_senha.grid(row=12, column=0, sticky="ew", padx=14, pady=1)
        self.btn_sair = ctk.CTkButton(
            menu, text="Sair", height=32, anchor="w", fg_color="transparent",
            text_color=("gray10", "gray90"), hover_color=("gray75", "gray25"),
            command=self.raiz.sair)
        self.btn_sair.grid(row=13, column=0, sticky="ew", padx=14, pady=1)
        self.sw_tema = ctk.CTkSwitch(menu, text="Modo escuro", command=self.alternar_tema)
        self.sw_tema.select()
        self.sw_tema.grid(row=14, column=0, sticky="w", padx=22, pady=(10, 20))

    def trocar_senha(self):
        DialogoSenha(self.raiz, "funcionario", self.usuario["_id"])

    def mostrar(self, nome):
        for outro, pagina in self.paginas.items():
            pagina.grid_remove()
            self.botoes_menu[outro].configure(fg_color="transparent")
        self.botoes_menu[nome].configure(fg_color=COR_DESTAQUE)
        self.paginas[nome].grid(row=0, column=0, sticky="nsew")
        self.paginas[nome].ao_mostrar()

    def alternar_tema(self):
        ctk.set_appearance_mode("dark" if self.sw_tema.get() else "light")
        aplicar_estilo_tabela()

    def status(self, texto, erro=False):
        cor = "#e74c3c" if erro else ("#2e8b57", "#4cc38a")
        self.lbl_status.configure(text=texto, text_color=cor)


class PainelAluno(ctk.CTkFrame):
    def __init__(self, raiz, aluno):
        super().__init__(raiz, fg_color="transparent")
        self.raiz = raiz
        self.aluno = aluno
        self.banco = raiz.banco
        self.grid_columnconfigure(0, weight=1)
        self.grid_rowconfigure(4, weight=1)

        corpo = ctk.CTkFrame(self, fg_color="transparent")
        corpo.grid(row=0, column=0, sticky="nsew", padx=40, pady=28)
        corpo.grid_columnconfigure(0, weight=1)
        corpo.grid_rowconfigure(4, weight=1)
        self.corpo = corpo

        cab = ctk.CTkFrame(corpo, fg_color="transparent")
        cab.grid(row=0, column=0, sticky="ew")
        cab.grid_columnconfigure(0, weight=1)
        self.lbl_nome = ctk.CTkLabel(cab, text="", anchor="w", font=ctk.CTkFont(size=28, weight="bold"))
        self.lbl_nome.grid(row=0, column=0, sticky="w")
        self.lbl_info = ctk.CTkLabel(cab, text="", anchor="w", text_color=("gray40", "gray60"))
        self.lbl_info.grid(row=1, column=0, sticky="w")
        ctk.CTkButton(cab, text="Trocar senha", width=130, height=36,
                      fg_color=("gray70", "gray30"), hover_color=("gray60", "gray40"),
                      text_color=("gray10", "gray90"), command=self.trocar_senha).grid(
            row=0, column=1, rowspan=2, padx=(0, 8))
        ctk.CTkButton(cab, text="Sair", width=90, height=36, fg_color=COR_ALUNO,
                      command=raiz.sair).grid(row=0, column=2, rowspan=2)

        self.faixa = ctk.CTkFrame(corpo, corner_radius=12)
        self.faixa.grid(row=1, column=0, sticky="ew", pady=(18, 0))
        self.lbl_geral = ctk.CTkLabel(self.faixa, text="", anchor="w", font=ctk.CTkFont(size=20, weight="bold"))
        self.lbl_geral.pack(anchor="w", padx=20, pady=16)

        self.valores = fazer_cartoes(corpo, 2, [
            ("total", "Disciplinas"), ("aprovado", "Aprovado"),
            ("exame", "Exame"), ("reprovado", "Reprovado")])
        ctk.CTkLabel(corpo, text="Minhas notas", anchor="w", font=ctk.CTkFont(size=16, weight="bold")).grid(
            row=3, column=0, sticky="w", pady=(18, 6))
        self.tabela = Tabela(corpo, [
            ("disciplina", "Disciplina", 300), ("b1", "1º bim", 80),
            ("b2", "2º bim", 80), ("b3", "3º bim", 80), ("b4", "4º bim", 80),
            ("media", "Média", 90), ("resultado", "Resultado", 150)])
        self.tabela.grid(row=4, column=0, sticky="nsew")
        ctk.CTkLabel(
            corpo, anchor="w", justify="left", wraplength=900,
            text_color=("gray40", "gray60"), font=ctk.CTkFont(size=12),
            text=f"Média {bd.formatar_nota(bd.NOTA_APROVACAO)} ou mais: aprovado | "
                 f"De {bd.formatar_nota(bd.NOTA_RECUPERACAO)} até menos de {bd.formatar_nota(bd.NOTA_APROVACAO)}: exame | "
                 f"Abaixo de {bd.formatar_nota(bd.NOTA_RECUPERACAO)}: reprovado.").grid(
            row=5, column=0, sticky="w", pady=(10, 0))
        self.atualizar()

    def atualizar(self):
        try:
            dados = self.banco.visao_do_aluno(self.aluno["_id"])
        except (ValueError, PyMongoError) as erro:
            messagebox.showerror("Erro", f"Não foi possível carregar suas notas:\n{erro}")
            return

        self.lbl_nome.configure(text=dados["nome"])
        self.lbl_info.configure(text=f"Matrícula {dados['matricula']}    {dados['curso']}")
        texto, resultado = dados["geral"]
        self.faixa.configure(fg_color=CORES_RESULTADO[resultado])
        self.lbl_geral.configure(text=texto, text_color="white")
        resultados = [l["resultado"] for l in dados["linhas"]]
        self.valores["total"].configure(text=str(len(resultados)))
        self.valores["aprovado"].configure(text=str(resultados.count(bd.RES_APROVADO)))
        self.valores["exame"].configure(text=str(resultados.count(bd.RES_EXAME)))
        self.valores["reprovado"].configure(text=str(resultados.count(bd.RES_REPROVADO)))
        self.tabela.preencher([
            (str(i), (l["disciplina"], *[bd.formatar_nota(b) for b in l["bimestres"]],
                      bd.formatar_nota(l["media"]), l["resultado"]), l["resultado"])
            for i, l in enumerate(dados["linhas"])])

    def trocar_senha(self):
        DialogoSenha(self.raiz, "aluno", self.aluno["_id"])


class App(ctk.CTk):
    def __init__(self):
        super().__init__()
        self.title("Sistema Escolar")
        self.geometry("1180x780")
        self.minsize(1080, 720)
        self.banco = bd.conectar()
        self.grid_columnconfigure(0, weight=1)
        self.grid_rowconfigure(0, weight=1)
        self.tela = None
        aplicar_estilo_tabela()
        self.mostrar_login()

    def trocar_tela(self, nova):
        antiga, self.tela = self.tela, nova
        nova.grid(row=0, column=0, sticky="nsew")
        if antiga is not None:
            antiga.destroy()

    def mostrar_login(self):
        self.trocar_tela(TelaLogin(self))

    def abrir_painel_escola(self, usuario):
        self.trocar_tela(PainelEscola(self, usuario))

    def abrir_painel_aluno(self, aluno):
        self.trocar_tela(PainelAluno(self, aluno))

    def sair(self):
        self.mostrar_login()


if __name__ == "__main__":
    App().mainloop()
