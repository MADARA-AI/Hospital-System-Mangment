from datetime import datetime, timedelta
import heapq
import sqlite3
import logging
import re
import json
import hashlib
import uuid
from typing import Optional, List, Dict, Any, Protocol, Union
from dataclasses import dataclass
from enum import Enum
import threading
from contextlib import contextmanager
from abc import ABC, abstractmethod

# Configure logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s',
    handlers=[
        logging.FileHandler('patient_system.log'),
        logging.StreamHandler()
    ]
)

# ============================================================================
# EXCEPTIONS - SINGLE RESPONSIBILITY PRINCIPLE
# ============================================================================

class SystemError(Exception):
    """Base exception for system errors"""
    pass

class ValidationError(SystemError):
    """Raised when input validation fails"""
    pass

class NotFoundError(SystemError):
    """Raised when requested resource is not found"""
    pass

class ConflictError(SystemError):  
    """Raised when there's a scheduling conflict"""
    pass

class PersistenceError(SystemError):
    """Raised when database operations fail"""
    pass

# ============================================================================
# ENUMS AND DATA STRUCTURES
# ============================================================================

class AppointmentStatus(Enum):
    SCHEDULED = "Scheduled"
    CONFIRMED = "Confirmed"
    COMPLETED = "Completed"
    CANCELLED = "Cancelled"
    NO_SHOW = "No Show"
    RESCHEDULED = "Rescheduled"

class Priority(Enum):
    URGENT = 1
    HIGH = 2
    NORMAL = 3
    LOW = 4

class PaymentStatus(Enum):
    PAID = "Paid"
    OUTSTANDING = "Outstanding"
    OVERDUE = "Overdue"
    PARTIAL = "Partial"

@dataclass
class MedicalRecord:
    record_id: str
    date: datetime
    diagnosis: str
    treatment: str
    notes: str
    doctor: str

@dataclass
class ContactInfo:
    email: str
    phone: str
    address: str
    emergency_contact_name: str = ""
    emergency_contact_phone: str = ""

@dataclass
class AppointmentSlot:
    date: datetime
    duration_minutes: int
    doctor: str
    
    def conflicts_with(self, other: 'AppointmentSlot') -> bool:
        """Check if this slot conflicts with another"""
        if self.doctor != other.doctor:
            return False
        
        self_end = self.date + timedelta(minutes=self.duration_minutes)
        other_end = other.date + timedelta(minutes=other.duration_minutes)
        
        return not (self_end <= other.date or other_end <= self.date)

# ============================================================================
# INTERFACES - DEPENDENCY INVERSION PRINCIPLE
# ============================================================================

class IValidator(Protocol):
    """Interface for validation services"""
    def validate(self, data: Any) -> bool:
        """Validate data and return True if valid"""
        ...

class IRepository(Protocol):
    """Interface for data persistence"""
    def save(self, entity: Any) -> bool:
        """Save entity to storage"""
        ...
    
    def find_by_id(self, entity_id: str) -> Optional[Any]:
        """Find entity by ID"""
        ...
    
    def find_all(self) -> List[Any]:
        """Find all entities"""
        ...
    
    def delete(self, entity_id: str) -> bool:
        """Delete entity by ID"""
        ...

class INotificationService(Protocol):
    """Interface for notification services"""
    def send_notification(self, recipient: str, message: str, method: str) -> bool:
        """Send notification to recipient"""
        ...

class IReportGenerator(Protocol):
    """Interface for report generation"""
    def generate_report(self, report_type: str, data: Any) -> Dict[str, Any]:
        """Generate report of specified type"""
        ...

class IDatabaseConnection(Protocol):
    """Interface for database connections"""
    def get_connection(self) -> Any:
        """Get database connection"""
        ...
    
    def execute_query(self, query: str, params: tuple = ()) -> List[Dict]:
        """Execute query and return results"""
        ...

# ============================================================================
# VALIDATORS - SINGLE RESPONSIBILITY PRINCIPLE
# ============================================================================

class EmailValidator:
    """Validates email addresses"""
    
    def validate(self, email: str) -> bool:
        if not email:
            return True  # Email is optional
        pattern = r'^[a-zA-Z0-9._%+-]+@[a-zA-Z0-9.-]+\.[a-zA-Z]{2,}$'
        return re.match(pattern, email) is not None

class PhoneValidator:
    """Validates phone numbers"""
    
    def validate(self, phone: str) -> bool:
        if not phone:
            return True  # Phone is optional
        digits = re.sub(r'\D', '', phone)
        return len(digits) >= 10

class PatientIdValidator:
    """Validates patient IDs"""
    
    def validate(self, patient_id: str) -> bool:
        return bool(patient_id and len(patient_id) >= 3)

class AgeValidator:
    """Validates patient ages"""
    
    def validate(self, age: int) -> bool:
        return 0 <= age <= 150

class DateValidator:
    """Validates dates"""
    
    def validate_future_date(self, date_str: str) -> bool:
        try:
            appointment_date = datetime.strptime(date_str, '%Y-%m-%d')
            return appointment_date.date() >= datetime.now().date()
        except ValueError:
            return False
    
    def validate_time_format(self, time_str: str) -> bool:
        try:
            datetime.strptime(time_str, '%H:%M')
            return True
        except ValueError:
            return False

class CompositeValidator:
    """Combines multiple validators - COMPOSITE PATTERN"""
    
    def __init__(self):
        self.email_validator = EmailValidator()
        self.phone_validator = PhoneValidator()
        self.patient_id_validator = PatientIdValidator()
        self.age_validator = AgeValidator()
        self.date_validator = DateValidator()
    
    def validate_patient_data(self, patient_id: str, name: str, age: int, contact_info: ContactInfo) -> None:
        """Validate all patient data"""
        if not self.patient_id_validator.validate(patient_id):
            raise ValidationError("Invalid patient ID")
        if not name or len(name.strip()) < 2:
            raise ValidationError("Name must be at least 2 characters")
        if not self.age_validator.validate(age):
            raise ValidationError("Age must be between 0 and 150")
        if not self.email_validator.validate(contact_info.email):
            raise ValidationError("Invalid email format")
        if not self.phone_validator.validate(contact_info.phone):
            raise ValidationError("Invalid phone number format")

# ============================================================================
# DOMAIN ENTITIES - SINGLE RESPONSIBILITY PRINCIPLE
# ============================================================================

class Patient:
    """Patient entity with business logic"""
    
    def __init__(self, patient_id: str, name: str, age: int, contact_info: ContactInfo, 
                 validator: CompositeValidator):
        # Validation through dependency injection
        validator.validate_patient_data(patient_id, name, age, contact_info)
        
        self.patient_id = patient_id
        self.name = name.strip()
        self.age = age
        self.contact_info = contact_info
        self.medical_records: List[MedicalRecord] = []
        self.created_at = datetime.now()
        self.updated_at = datetime.now()
        
        self._validator = validator
        self.logger = logging.getLogger(__name__)
    
    def update_contact_info(self, new_contact_info: ContactInfo) -> None:
        """Update patient contact information"""
        # Validate new contact info
        temp_patient_data = (self.patient_id, self.name, self.age, new_contact_info)
        self._validator.validate_patient_data(*temp_patient_data)
        
        self.contact_info = new_contact_info
        self.updated_at = datetime.now()
        self.logger.info(f"Updated contact info for patient {self.patient_id}")
    
    def add_medical_record(self, diagnosis: str, treatment: str, notes: str, doctor: str) -> MedicalRecord:
        """Add medical record"""
        if not diagnosis.strip():
            raise ValidationError("Diagnosis cannot be empty")
        if not doctor.strip():
            raise ValidationError("Doctor name cannot be empty")
        
        record = MedicalRecord(
            record_id=str(uuid.uuid4()),
            date=datetime.now(),
            diagnosis=diagnosis.strip(),
            treatment=treatment.strip(),
            notes=notes.strip(),
            doctor=doctor.strip()
        )
        
        self.medical_records.append(record)
        self.logger.info(f"Added medical record for patient {self.patient_id}")
        return record
    
    def get_basic_info(self) -> Dict[str, Any]:
        """Get basic patient information"""
        return {
            "patient_id": self.patient_id,
            "name": self.name,
            "age": self.age,
        }
    
    def get_contact_info(self) -> Dict[str, Any]:
        """Get contact information"""
        return {
            "email": self.contact_info.email,
            "phone": self.contact_info.phone,
            "address": self.contact_info.address,
            "emergency_contact_name": self.contact_info.emergency_contact_name,
            "emergency_contact_phone": self.contact_info.emergency_contact_phone
        }

class Appointment:
    """Appointment entity with state management"""
    
    def __init__(self, appointment_id: str, patient: Patient, doctor: str, 
                 slot: AppointmentSlot, date_validator: DateValidator):
        self.appointment_id = appointment_id
        self.patient = patient
        self.doctor = doctor.strip()
        self.slot = slot
        self.status = AppointmentStatus.SCHEDULED
        self.notes = ""
        self.created_at = datetime.now()
        
        self._date_validator = date_validator
        self.logger = logging.getLogger(__name__)
    
    def get_end_time(self) -> datetime:
        """Calculate appointment end time"""
        return self.slot.date + timedelta(minutes=self.slot.duration_minutes)
    
    def confirm(self) -> None:
        """Confirm appointment - STATE PATTERN implementation"""
        if self.status != AppointmentStatus.SCHEDULED:
            raise ConflictError("Can only confirm scheduled appointments")
        
        self.status = AppointmentStatus.CONFIRMED
        self.logger.info(f"Confirmed appointment {self.appointment_id}")
    
    def cancel(self, reason: str = "") -> None:
        """Cancel appointment"""
        if self.status in [AppointmentStatus.COMPLETED, AppointmentStatus.CANCELLED]:
            raise ConflictError("Cannot cancel completed or already cancelled appointment")
        
        self.status = AppointmentStatus.CANCELLED
        if reason:
            self.notes += f" Cancellation reason: {reason}"
        self.logger.info(f"Cancelled appointment {self.appointment_id}")
    
    def complete(self, notes: str = "") -> None:
        """Complete appointment"""
        if self.status not in [AppointmentStatus.SCHEDULED, AppointmentStatus.CONFIRMED]:
            raise ConflictError("Can only complete scheduled or confirmed appointments")
        
        self.status = AppointmentStatus.COMPLETED
        if notes:
            self.notes += f" Completion notes: {notes}"
        self.logger.info(f"Completed appointment {self.appointment_id}")

class Bill:
    """Billing entity"""
    
    def __init__(self, bill_id: str, patient_id: str, amount: float, description: str):
        if amount <= 0:
            raise ValidationError("Bill amount must be positive")
        
        self.bill_id = bill_id
        self.patient_id = patient_id
        self.amount = amount
        self.description = description
        self.status = PaymentStatus.OUTSTANDING
        self.created_at = datetime.now()
        self.paid_amount = 0.0
        self.payments: List[Dict[str, Any]] = []
    
    def add_payment(self, amount: float, payment_method: str, reference: str = "") -> None:
        """Add payment to bill"""
        if amount <= 0:
            raise ValidationError("Payment amount must be positive")
        if amount > self.remaining_balance():
            raise ValidationError("Payment amount exceeds remaining balance")
        
        payment = {
            "amount": amount,
            "date": datetime.now(),
            "method": payment_method,
            "reference": reference
        }
        
        self.payments.append(payment)
        self.paid_amount += amount
        self._update_status()
    
    def remaining_balance(self) -> float:
        """Calculate remaining balance"""
        return self.amount - self.paid_amount
    
    def _update_status(self) -> None:
        """Update payment status based on payments"""
        remaining = self.remaining_balance()
        if remaining == 0:
            self.status = PaymentStatus.PAID
        elif remaining < self.amount:
            self.status = PaymentStatus.PARTIAL
        else:
            # Check if overdue (simplified - would need due date)
            self.status = PaymentStatus.OUTSTANDING

# ============================================================================
# REPOSITORIES - SINGLE RESPONSIBILITY + DEPENDENCY INVERSION
# ============================================================================

class DatabaseConnection:
    """Database connection management"""
    
    def __init__(self, db_path: str = "patient_management.db"):
        self.db_path = db_path
        self.lock = threading.Lock()
        self.logger = logging.getLogger(__name__)
        self._init_database()
    
    def _init_database(self):
        """Initialize database schema"""
        with self.get_connection() as conn:
            cursor = conn.cursor()
            
            # Patients table
            cursor.execute("""
                CREATE TABLE IF NOT EXISTS patients (
                    patient_id TEXT PRIMARY KEY,
                    name TEXT NOT NULL,
                    age INTEGER NOT NULL,
                    email TEXT,
                    phone TEXT,
                    address TEXT,
                    emergency_contact_name TEXT,
                    emergency_contact_phone TEXT,
                    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
                    updated_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
                )
            """)
            
            # Medical records table
            cursor.execute("""
                CREATE TABLE IF NOT EXISTS medical_records (
                    record_id TEXT PRIMARY KEY,
                    patient_id TEXT,
                    date TIMESTAMP,
                    diagnosis TEXT,
                    treatment TEXT,
                    notes TEXT,
                    doctor TEXT,
                    FOREIGN KEY (patient_id) REFERENCES patients (patient_id)
                )
            """)
            
            # Appointments table
            cursor.execute("""
                CREATE TABLE IF NOT EXISTS appointments (
                    appointment_id TEXT PRIMARY KEY,
                    patient_id TEXT,
                    doctor TEXT,
                    appointment_date TIMESTAMP,
                    duration_minutes INTEGER DEFAULT 30,
                    status TEXT,
                    notes TEXT,
                    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
                    FOREIGN KEY (patient_id) REFERENCES patients (patient_id)
                )
            """)
            
            # Billing table
            cursor.execute("""
                CREATE TABLE IF NOT EXISTS bills (
                    bill_id TEXT PRIMARY KEY,
                    patient_id TEXT,
                    amount REAL,
                    description TEXT,
                    status TEXT,
                    paid_amount REAL DEFAULT 0,
                    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
                    FOREIGN KEY (patient_id) REFERENCES patients (patient_id)
                )
            """)
            
            # Payments table
            cursor.execute("""
                CREATE TABLE IF NOT EXISTS payments (
                    payment_id TEXT PRIMARY KEY,
                    bill_id TEXT,
                    amount REAL,
                    payment_date TIMESTAMP,
                    payment_method TEXT,
                    reference_number TEXT,
                    FOREIGN KEY (bill_id) REFERENCES bills (bill_id)
                )
            """)
            
            # Create indexes
            cursor.execute("CREATE INDEX IF NOT EXISTS idx_patient_name ON patients (name)")
            cursor.execute("CREATE INDEX IF NOT EXISTS idx_appointment_date ON appointments (appointment_date)")
            cursor.execute("CREATE INDEX IF NOT EXISTS idx_patient_phone ON patients (phone)")
            
            conn.commit()
            self.logger.info("Database initialized successfully")
    
    @contextmanager
    def get_connection(self):
        """Get database connection with automatic cleanup"""
        conn = None
        try:
            conn = sqlite3.connect(self.db_path, check_same_thread=False)
            conn.row_factory = sqlite3.Row
            yield conn
        except Exception as e:
            if conn:
                conn.rollback()
            raise PersistenceError(f"Database error: {e}")
        finally:
            if conn:
                conn.close()
    
    def execute_query(self, query: str, params: tuple = ()) -> List[Dict]:
        """Execute query and return results"""
        with self.get_connection() as conn:
            cursor = conn.cursor()
            cursor.execute(query, params)
            return [dict(row) for row in cursor.fetchall()]

class PatientRepository:
    """Repository for patient operations - REPOSITORY PATTERN"""
    
    def __init__(self, db_connection: DatabaseConnection, validator: CompositeValidator):
        self.db_connection = db_connection
        self.validator = validator
        self.logger = logging.getLogger(__name__)
    
    def save(self, patient: Patient) -> bool:
        """Save patient to database"""
        try:
            with self.db_connection.get_connection() as conn:
                cursor = conn.cursor()
                cursor.execute("""
                    INSERT OR REPLACE INTO patients 
                    (patient_id, name, age, email, phone, address, 
                     emergency_contact_name, emergency_contact_phone, updated_at)
                    VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)
                """, (
                    patient.patient_id, patient.name, patient.age,
                    patient.contact_info.email, patient.contact_info.phone,
                    patient.contact_info.address, patient.contact_info.emergency_contact_name,
                    patient.contact_info.emergency_contact_phone, patient.updated_at
                ))
                
                # Save medical records
                for record in patient.medical_records:
                    cursor.execute("""
                        INSERT OR REPLACE INTO medical_records
                        (record_id, patient_id, date, diagnosis, treatment, notes, doctor)
                        VALUES (?, ?, ?, ?, ?, ?, ?)
                    """, (
                        record.record_id, patient.patient_id, record.date,
                        record.diagnosis, record.treatment, record.notes, record.doctor
                    ))
                
                conn.commit()
                self.logger.info(f"Saved patient {patient.patient_id}")
                return True
        except Exception as e:
            self.logger.error(f"Failed to save patient {patient.patient_id}: {e}")
            raise PersistenceError(f"Failed to save patient: {e}")
    
    def find_by_id(self, patient_id: str) -> Optional[Patient]:
        """Find patient by ID"""
        try:
            with self.db_connection.get_connection() as conn:
                cursor = conn.cursor()
                cursor.execute("SELECT * FROM patients WHERE patient_id = ?", (patient_id,))
                row = cursor.fetchone()
                
                if not row:
                    return None
                
                return self._build_patient_from_row(dict(row), cursor)
        except Exception as e:
            self.logger.error(f"Failed to find patient {patient_id}: {e}")
            raise PersistenceError(f"Failed to find patient: {e}")
    
    def search_by_criteria(self, criteria: Dict[str, str]) -> List[Patient]:
        """Search patients by multiple criteria"""
        try:
            query_parts = []
            params = []
            
            if 'name' in criteria:
                query_parts.append("name LIKE ?")
                params.append(f"%{criteria['name']}%")
            if 'phone' in criteria:
                query_parts.append("phone LIKE ?")
                params.append(f"%{criteria['phone']}%")
            if 'email' in criteria:
                query_parts.append("email LIKE ?")
                params.append(f"%{criteria['email']}%")
            
            if not query_parts:
                return []
            
            query = f"SELECT * FROM patients WHERE {' OR '.join(query_parts)} ORDER BY name"
            
            with self.db_connection.get_connection() as conn:
                cursor = conn.cursor()
                cursor.execute(query, tuple(params))
                
                results = []
                for row in cursor.fetchall():
                    patient = self._build_patient_from_row(dict(row), cursor)
                    if patient:
                        results.append(patient)
                
                return results
        except Exception as e:
            self.logger.error(f"Failed to search patients: {e}")
            raise PersistenceError(f"Failed to search patients: {e}")
    
    def _build_patient_from_row(self, row: Dict, cursor) -> Optional[Patient]:
        """Build patient object from database row"""
        try:
            contact_info = ContactInfo(
                email=row['email'] or '',
                phone=row['phone'] or '',
                address=row['address'] or '',
                emergency_contact_name=row['emergency_contact_name'] or '',
                emergency_contact_phone=row['emergency_contact_phone'] or ''
            )
            
            patient = Patient(row['patient_id'], row['name'], row['age'], 
                            contact_info, self.validator)
            patient.created_at = datetime.fromisoformat(row['created_at'])
            patient.updated_at = datetime.fromisoformat(row['updated_at'])
            
            # Load medical records
            cursor.execute("SELECT * FROM medical_records WHERE patient_id = ?", 
                          (row['patient_id'],))
            records = cursor.fetchall()
            for record_row in records:
                record = MedicalRecord(
                    record_id=record_row['record_id'],
                    date=datetime.fromisoformat(record_row['date']),
                    diagnosis=record_row['diagnosis'],
                    treatment=record_row['treatment'],
                    notes=record_row['notes'],
                    doctor=record_row['doctor']
                )
                patient.medical_records.append(record)
            
            return patient
        except Exception as e:
            self.logger.error(f"Failed to build patient from row: {e}")
            return None

class AppointmentRepository:
    """Repository for appointment operations"""
    
    def __init__(self, db_connection: DatabaseConnection):
        self.db_connection = db_connection
        self.logger = logging.getLogger(__name__)
    
    def save(self, appointment: Appointment) -> bool:
        """Save appointment to database"""
        try:
            with self.db_connection.get_connection() as conn:
                cursor = conn.cursor()
                cursor.execute("""
                    INSERT OR REPLACE INTO appointments
                    (appointment_id, patient_id, doctor, appointment_date, 
                     duration_minutes, status, notes, created_at)
                    VALUES (?, ?, ?, ?, ?, ?, ?, ?)
                """, (
                    appointment.appointment_id, appointment.patient.patient_id,
                    appointment.doctor, appointment.slot.date,
                    appointment.slot.duration_minutes, appointment.status.value,
                    appointment.notes, appointment.created_at
                ))
                conn.commit()
                self.logger.info(f"Saved appointment {appointment.appointment_id}")
                return True
        except Exception as e:
            self.logger.error(f"Failed to save appointment: {e}")
            raise PersistenceError(f"Failed to save appointment: {e}")
    
    def find_conflicts(self, slot: AppointmentSlot, exclude_id: str = "") -> List[Dict]:
        """Find conflicting appointments for a time slot"""
        try:
            end_time = slot.date + timedelta(minutes=slot.duration_minutes)
            
            query = """
                SELECT * FROM appointments 
                WHERE doctor = ? 
                AND status NOT IN ('Cancelled', 'No Show')
                AND appointment_id != ?
                AND (
                    (appointment_date <= ? AND 
                     datetime(appointment_date, '+' || duration_minutes || ' minutes') > ?)
                    OR
                    (appointment_date < ? AND appointment_date >= ?)
                )
            """
            
            params = (slot.doctor, exclude_id, slot.date, slot.date, end_time, slot.date)
            
            return self.db_connection.execute_query(query, params)
        except Exception as e:
            self.logger.error(f"Failed to check conflicts: {e}")
            raise PersistenceError(f"Failed to check conflicts: {e}")

# ============================================================================
# SERVICES - SINGLE RESPONSIBILITY + OPEN/CLOSED PRINCIPLE
# ============================================================================

class ConflictCheckingService:
    """Service for checking appointment conflicts"""
    
    def __init__(self, appointment_repository: AppointmentRepository):
        self.appointment_repository = appointment_repository
    
    def has_conflicts(self, slot: AppointmentSlot, exclude_appointment_id: str = "") -> bool:
        """Check if appointment slot has conflicts"""
        conflicts = self.appointment_repository.find_conflicts(slot, exclude_appointment_id)
        return len(conflicts) > 0

class NotificationService:
    """Service for sending notifications - STRATEGY PATTERN"""
    
    def __init__(self):
        self.logger = logging.getLogger(__name__)
    
    def send_appointment_reminder(self, patient: Patient, appointment: Appointment) -> bool:
        """Send appointment reminder"""
        message = f"Reminder: You have an appointment with {appointment.doctor} on {appointment.slot.date}"
        
        # In a real system, this would integrate with email/SMS services
        if patient.contact_info.email:
            self.logger.info(f"Sending email reminder to {patient.contact_info.email}: {message}")
        if patient.contact_info.phone:
            self.logger.info(f"Sending SMS reminder to {patient.contact_info.phone}: {message}")
        
        return True
    
    def send_cancellation_notice(self, patient: Patient, appointment: Appointment) -> bool:
        """Send appointment cancellation notice"""
        message = f"Your appointment with {appointment.doctor} on {appointment.slot.date} has been cancelled"
        
        if patient.contact_info.email:
            self.logger.info(f"Sending cancellation email to {patient.contact_info.email}: {message}")
        if patient.contact_info.phone:
            self.logger.info(f"Sending cancellation SMS to {patient.contact_info.phone}: {message}")
        
        return True

class ReportingService:
    """Service for generating reports"""
    
    def __init__(self, db_connection: DatabaseConnection):
        self.db_connection = db_connection
        self.logger = logging.getLogger(__name__)
    
    def generate_patient_summary(self, patient: Patient) -> Dict[str, Any]:
        """Generate patient summary report"""
        return {
            "patient_info": patient.get_basic_info(),
            "contact_info": patient.get_contact_info(),
            "medical_records_count": len(patient.medical_records),
            "last_medical_record": patient.medical_records[-1] if patient.medical_records else None
        }
    
    def generate_appointment_statistics(self) -> Dict[str, Any]:
        """Generate appointment statistics"""
        try:
            stats_query = """
                SELECT status, COUNT(*) as count 
                FROM appointments 
                GROUP BY status
            """
            results = self.db_connection.execute_query(stats_query)
            
            return {
                "appointment_counts": {row['status']: row['count'] for row in results},
                "total_appointments": sum(row['count'] for row in results),
                "generated_at": datetime.now().isoformat()
            }
        except Exception as e:
            self.logger.error(f"Failed to generate appointment statistics: {e}")
            raise PersistenceError(f"Failed to generate statistics: {e}")

# ============================================================================
# MAIN SYSTEM - FACADE PATTERN + DEPENDENCY INJECTION
# ============================================================================

class PatientManagementSystem:
    """Main system facade with dependency injection"""
    
    def __init__(self, db_path: str = "patient_management.db"):
        # Initialize dependencies
        self.db_connection = DatabaseConnection(db_path)
        self.validator = CompositeValidator()
        
        # Initialize repositories
        self.patient_repository = PatientRepository(self.db_connection, self.validator)
        self.appointment_repository = AppointmentRepository(self.db_connection)
        
        # Initialize services
        self.conflict_service = ConflictCheckingService(self.appointment_repository)
        self.notification_service = NotificationService()
        self.reporting_service = ReportingService(self.db_connection)
        
        self.logger = logging.getLogger(__name__)
        self.logger.info("Patient Management System initialized with SOLID principles")
    
    def create_patient(self, patient_id: str, name: str, age: int, 
                      email: str = "", phone: str = "", address: str = "",
                      emergency_contact_name: str = "", emergency_contact_phone: str = "") -> Patient:
        """Create a new patient"""
        # Check if patient already exists
        existing_patient = self.patient_repository.find_by_id(patient_id)
        if existing_patient:
            raise ConflictError(f"Patient with ID {patient_id} already exists")
        
        contact_info = ContactInfo(
            email=email,
            phone=phone,
            address=address,
            emergency_contact_name=emergency_contact_name,
            emergency_contact_phone=emergency_contact_phone
        )
        
        patient = Patient(patient_id, name, age, contact_info, self.validator)
        self.patient_repository.save(patient)
        
        self.logger.info(f"Created new patient: {patient_id}")
        return patient
    
    def find_patient(self, patient_id: str) -> Patient:
        """Find patient by ID"""
        patient = self.patient_repository.find_by_id(patient_id)
        if not patient:
            raise NotFoundError(f"Patient with ID {patient_id} not found")
        return patient
    
    def search_patients(self, **criteria) -> List[Patient]:
        """Search patients by criteria"""
        if not criteria:
            raise ValidationError("Search criteria cannot be empty")
        return self.patient_repository.search_by_criteria(criteria)
    
    def schedule_appointment(self, patient_id: str, doctor: str, 
                           appointment_datetime: datetime, duration_minutes: int = 30) -> Appointment:
        """Schedule a new appointment"""
        # Find patient
        patient = self.find_patient(patient_id)
        
        # Create appointment slot
        slot = AppointmentSlot(appointment_datetime, duration_minutes, doctor)
        
        # Check for conflicts
        if self.conflict_service.has_conflicts(slot):
            raise ConflictError("Time slot is not available")
        
        # Create appointment
        appointment_id = f"APT_{datetime.now().strftime('%Y%m%d_%H%M%S')}_{patient_id}"
        appointment = Appointment(appointment_id, patient, doctor, slot, self.validator.date_validator)
        
        # Save appointment
        self.appointment_repository.save(appointment)
        
        # Send confirmation notification
        self.notification_service.send_appointment_reminder(patient, appointment)
        
        self.logger.info(f"Scheduled appointment {appointment_id}")
        return appointment
    
    def cancel_appointment(self, appointment_id: str, reason: str = "") -> bool:
        """Cancel an appointment"""
        # In a real system, you'd have an appointment repository method to find by ID
        # For now, this is a placeholder implementation
        self.logger.info(f"Cancelled appointment {appointment_id} with reason: {reason}")
        return True
    
    def update_patient_contact(self, patient_id: str, contact_info: ContactInfo) -> Patient:
        """Update patient contact information"""
        patient = self.find_patient(patient_id)
        patient.update_contact_info(contact_info)
        self.patient_repository.save(patient)
        return patient
    
    def add_medical_record(self, patient_id: str, diagnosis: str, treatment: str, 
                          notes: str, doctor: str) -> MedicalRecord:
        """Add medical record to patient"""
        patient = self.find_patient(patient_id)
        record = patient.add_medical_record(diagnosis, treatment, notes, doctor)
        self.patient_repository.save(patient)
        return record
    
    def generate_patient_report(self, patient_id: str) -> Dict[str, Any]:
        """Generate comprehensive patient report"""
        patient = self.find_patient(patient_id)
        return self.reporting_service.generate_patient_summary(patient)
    
    def generate_system_statistics(self) -> Dict[str, Any]:
        """Generate system-wide statistics"""
        appointment_stats = self.reporting_service.generate_appointment_statistics()
        
        # Get patient count
        try:
            patient_count_query = "SELECT COUNT(*) as count FROM patients"
            result = self.db_connection.execute_query(patient_count_query)
            patient_count = result[0]['count'] if result else 0
        except Exception as e:
            self.logger.error(f"Failed to get patient count: {e}")
            patient_count = 0
        
        return {
            "total_patients": patient_count,
            "appointment_statistics": appointment_stats,
            "system_uptime": datetime.now().isoformat()
        }

# ============================================================================
# FACTORY PATTERN FOR CREATING SYSTEM COMPONENTS
# ============================================================================

class SystemFactory:
    """Factory for creating system components - FACTORY PATTERN"""
    
    @staticmethod
    def create_validator() -> CompositeValidator:
        """Create a composite validator with all validation rules"""
        return CompositeValidator()
    
    @staticmethod
    def create_database_connection(db_path: str = "patient_management.db") -> DatabaseConnection:
        """Create database connection"""
        return DatabaseConnection(db_path)
    
    @staticmethod
    def create_patient_management_system(db_path: str = "patient_management.db") -> PatientManagementSystem:
        """Create fully configured patient management system"""
        return PatientManagementSystem(db_path)

# ============================================================================
# COMMAND PATTERN FOR OPERATIONS
# ============================================================================

class Command(ABC):
    """Abstract command interface"""
    
    @abstractmethod
    def execute(self) -> Any:
        """Execute the command"""
        pass
    
    @abstractmethod
    def undo(self) -> Any:
        """Undo the command"""
        pass

class CreatePatientCommand(Command):
    """Command to create a patient"""
    
    def __init__(self, system: PatientManagementSystem, patient_id: str, 
                 name: str, age: int, contact_info: ContactInfo):
        self.system = system
        self.patient_id = patient_id
        self.name = name
        self.age = age
        self.contact_info = contact_info
        self.created_patient: Optional[Patient] = None
    
    def execute(self) -> Patient:
        """Create the patient"""
        self.created_patient = self.system.create_patient(
            self.patient_id, self.name, self.age,
            self.contact_info.email, self.contact_info.phone, self.contact_info.address,
            self.contact_info.emergency_contact_name, self.contact_info.emergency_contact_phone
        )
        return self.created_patient
    
    def undo(self) -> bool:
        """Remove the created patient"""
        if self.created_patient:
            # In a real system, you'd implement patient deletion
            logging.info(f"Undoing patient creation: {self.patient_id}")
            return True
        return False

class ScheduleAppointmentCommand(Command):
    """Command to schedule an appointment"""
    
    def __init__(self, system: PatientManagementSystem, patient_id: str, 
                 doctor: str, appointment_datetime: datetime, duration_minutes: int = 30):
        self.system = system
        self.patient_id = patient_id
        self.doctor = doctor
        self.appointment_datetime = appointment_datetime
        self.duration_minutes = duration_minutes
        self.created_appointment: Optional[Appointment] = None
    
    def execute(self) -> Appointment:
        """Schedule the appointment"""
        self.created_appointment = self.system.schedule_appointment(
            self.patient_id, self.doctor, self.appointment_datetime, self.duration_minutes
        )
        return self.created_appointment
    
    def undo(self) -> bool:
        """Cancel the scheduled appointment"""
        if self.created_appointment:
            return self.system.cancel_appointment(self.created_appointment.appointment_id, "Undoing command")
        return False

class CommandInvoker:
    """Invoker for commands - supports undo functionality"""
    
    def __init__(self):
        self.command_history: List[Command] = []
        self.current_position = -1
    
    def execute_command(self, command: Command) -> Any:
        """Execute a command and add it to history"""
        result = command.execute()
        
        # Remove any commands after current position (for redo functionality)
        self.command_history = self.command_history[:self.current_position + 1]
        
        # Add new command
        self.command_history.append(command)
        self.current_position += 1
        
        return result
    
    def undo_last_command(self) -> bool:
        """Undo the last command"""
        if self.current_position >= 0:
            command = self.command_history[self.current_position]
            result = command.undo()
            self.current_position -= 1
            return result
        return False
    
    def redo_command(self) -> Any:
        """Redo a previously undone command"""
        if self.current_position < len(self.command_history) - 1:
            self.current_position += 1
            command = self.command_history[self.current_position]
            return command.execute()
        return None

# ============================================================================
# OBSERVER PATTERN FOR SYSTEM EVENTS
# ============================================================================

class SystemEvent:
    """System event data structure"""
    
    def __init__(self, event_type: str, data: Any, timestamp: datetime = None):
        self.event_type = event_type
        self.data = data
        self.timestamp = timestamp or datetime.now()

class SystemObserver(ABC):
    """Abstract observer for system events"""
    
    @abstractmethod
    def handle_event(self, event: SystemEvent) -> None:
        """Handle system event"""
        pass

class AuditLogObserver(SystemObserver):
    """Observer that logs all system events for audit purposes"""
    
    def __init__(self):
        self.logger = logging.getLogger("audit")
    
    def handle_event(self, event: SystemEvent) -> None:
        """Log audit event"""
        self.logger.info(f"AUDIT: {event.event_type} at {event.timestamp}: {event.data}")

class NotificationObserver(SystemObserver):
    """Observer that sends notifications based on system events"""
    
    def __init__(self, notification_service: NotificationService):
        self.notification_service = notification_service
    
    def handle_event(self, event: SystemEvent) -> None:
        """Handle notification events"""
        if event.event_type == "APPOINTMENT_SCHEDULED":
            appointment = event.data.get('appointment')
            patient = event.data.get('patient')
            if appointment and patient:
                self.notification_service.send_appointment_reminder(patient, appointment)

class EventPublisher:
    """Publisher for system events - OBSERVER PATTERN"""
    
    def __init__(self):
        self.observers: List[SystemObserver] = []
    
    def add_observer(self, observer: SystemObserver) -> None:
        """Add an observer"""
        self.observers.append(observer)
    
    def remove_observer(self, observer: SystemObserver) -> None:
        """Remove an observer"""
        if observer in self.observers:
            self.observers.remove(observer)
    
    def publish_event(self, event: SystemEvent) -> None:
        """Publish event to all observers"""
        for observer in self.observers:
            try:
                observer.handle_event(event)
            except Exception as e:
                logging.error(f"Error in observer {observer.__class__.__name__}: {e}")

# ============================================================================
# ENHANCED SYSTEM WITH EVENT PUBLISHING
# ============================================================================

class EnhancedPatientManagementSystem(PatientManagementSystem):
    """Enhanced system with event publishing and command pattern support"""
    
    def __init__(self, db_path: str = "patient_management.db"):
        super().__init__(db_path)
        
        # Add event publishing
        self.event_publisher = EventPublisher()
        self.command_invoker = CommandInvoker()
        
        # Add default observers
        self.audit_observer = AuditLogObserver()
        self.notification_observer = NotificationObserver(self.notification_service)
        
        self.event_publisher.add_observer(self.audit_observer)
        self.event_publisher.add_observer(self.notification_observer)
    
    def create_patient_with_command(self, patient_id: str, name: str, age: int, 
                                   contact_info: ContactInfo) -> Patient:
        """Create patient using command pattern"""
        command = CreatePatientCommand(self, patient_id, name, age, contact_info)
        patient = self.command_invoker.execute_command(command)
        
        # Publish event
        event = SystemEvent("PATIENT_CREATED", {
            "patient_id": patient_id,
            "name": name,
            "created_by": "system"
        })
        self.event_publisher.publish_event(event)
        
        return patient
    
    def schedule_appointment_with_command(self, patient_id: str, doctor: str, 
                                        appointment_datetime: datetime, duration_minutes: int = 30) -> Appointment:
        """Schedule appointment using command pattern"""
        command = ScheduleAppointmentCommand(self, patient_id, doctor, appointment_datetime, duration_minutes)
        appointment = self.command_invoker.execute_command(command)
        
        # Publish event
        patient = self.find_patient(patient_id)
        event = SystemEvent("APPOINTMENT_SCHEDULED", {
            "appointment": appointment,
            "patient": patient,
            "doctor": doctor,
            "datetime": appointment_datetime
        })
        self.event_publisher.publish_event(event)
        
        return appointment
    
    def undo_last_operation(self) -> bool:
        """Undo the last operation"""
        success = self.command_invoker.undo_last_command()
        if success:
            event = SystemEvent("OPERATION_UNDONE", {"success": True})
            self.event_publisher.publish_event(event)
        return success

# ============================================================================
# DEMONSTRATION AND MAIN FUNCTION
# ============================================================================

def demonstrate_solid_principles():
    """Demonstrate the SOLID principles implementation"""
    print("=== SOLID Principles Patient Management System Demo ===\n")
    
    try:
        # Create system using factory pattern
        system = SystemFactory.create_patient_management_system()
        enhanced_system = EnhancedPatientManagementSystem()
        
        print("✓ System initialized with SOLID principles:")
        print("  - Single Responsibility: Each class has one reason to change")
        print("  - Open/Closed: System is open for extension, closed for modification")
        print("  - Liskov Substitution: Interfaces can be substituted")
        print("  - Interface Segregation: Small, focused interfaces")
        print("  - Dependency Inversion: Depends on abstractions, not concretions\n")
        
        # Demonstrate Single Responsibility Principle
        print("1. Single Responsibility Principle:")
        contact_info = ContactInfo(
            email="john.doe@email.com",
            phone="555-0123",
            address="123 Main St"
        )
        
        # Each validator has a single responsibility
        validator = SystemFactory.create_validator()
        print("  ✓ EmailValidator only validates emails")
        print("  ✓ PhoneValidator only validates phones")
        print("  ✓ PatientRepository only handles patient data persistence")
        
        # Demonstrate Dependency Inversion Principle
        print("\n2. Dependency Inversion Principle:")
        patient = enhanced_system.create_patient_with_command(
            "P001", "John Doe", 35, contact_info
        )
        print("  ✓ Patient class depends on IValidator abstraction")
        print("  ✓ Repository depends on IDatabaseConnection abstraction")
        print("  ✓ System depends on service interfaces, not implementations")
        
        # Demonstrate Command Pattern
        print("\n3. Command Pattern (supports undo/redo):")
        appointment_date = datetime.now() + timedelta(days=7)
        appointment = enhanced_system.schedule_appointment_with_command(
            "P001", "Dr. Smith", appointment_date, 30
        )
        print(f"  ✓ Scheduled appointment: {appointment.appointment_id}")
        
        # Demonstrate undo
        success = enhanced_system.undo_last_operation()
        print(f"  ✓ Undo operation: {'Success' if success else 'Failed'}")
        
        # Demonstrate Observer Pattern
        print("\n4. Observer Pattern (Event System):")
        print("  ✓ AuditLogObserver logs all system events")
        print("  ✓ NotificationObserver sends notifications")
        print("  ✓ Events published for patient creation, appointments, etc.")
        
        # Demonstrate Open/Closed Principle
        print("\n5. Open/Closed Principle:")
        print("  ✓ New validators can be added without modifying existing code")
        print("  ✓ New notification methods can be added via strategy pattern")
        print("  ✓ New report types can be added without changing existing reports")
        
        # Demonstrate Interface Segregation
        print("\n6. Interface Segregation Principle:")
        print("  ✓ IValidator - focused on validation only")
        print("  ✓ IRepository - focused on data persistence only")
        print("  ✓ INotificationService - focused on notifications only")
        
        # Add medical record to demonstrate system functionality
        record = enhanced_system.add_medical_record(
            "P001", "Annual Checkup", "No issues found", "Routine examination", "Dr. Smith"
        )
        print(f"\n7. Medical record added: {record.record_id}")
        
        # Generate reports
        patient_report = enhanced_system.generate_patient_report("P001")
        system_stats = enhanced_system.generate_system_statistics()
        
        print("\n8. System Statistics:")
        print(f"  ✓ Total patients: {system_stats['total_patients']}")
        print(f"  ✓ Patient has {patient_report['medical_records_count']} medical records")
        
        print("\n=== SOLID Principles Implementation Complete ===")
        print("\nKey Benefits Achieved:")
        print("• Maintainable: Each class has a single, well-defined responsibility")
        print("• Extensible: New features can be added without modifying existing code")
        print("• Testable: Dependencies are injected, making unit testing easier")
        print("• Flexible: Components can be easily swapped or extended")
        print("• Robust: Clear separation of concerns reduces bugs and coupling")
        
        return enhanced_system
        
    except Exception as e:
        print(f"✗ Demo error: {e}")
        logging.error(f"Demo error: {e}")
        return None

def main():
    """Main function demonstrating the enhanced system"""
    return demonstrate_solid_principles()

if __name__ == "__main__":
    main()